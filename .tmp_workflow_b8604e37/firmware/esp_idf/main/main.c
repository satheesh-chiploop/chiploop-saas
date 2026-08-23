#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include "driver/spi_master.h"
#include "esp_check.h"
#include "esp_heap_caps.h"
#include "esp_rom_sys.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"

#define CHIPLOOP_SPI_HOST SPI2_HOST
#define CHIPLOOP_PIN_SCLK 14
#define CHIPLOOP_PIN_MOSI 15
#define CHIPLOOP_PIN_MISO 2
#define CHIPLOOP_PIN_CS 13
#define CHIPLOOP_FRAME_BYTES 39
#define CHIPLOOP_SPI_CLOCK_HZ 10000000

static spi_device_handle_t chiploop_fpga;
static uint8_t *chiploop_tx_dma;
static uint8_t *chiploop_rx_dma;
static SemaphoreHandle_t chiploop_exchange_lock;

static esp_err_t chiploop_fpga_init(void) {
    const spi_bus_config_t bus = {
        .mosi_io_num = CHIPLOOP_PIN_MOSI, .miso_io_num = CHIPLOOP_PIN_MISO,
        .sclk_io_num = CHIPLOOP_PIN_SCLK, .quadwp_io_num = -1,
        .quadhd_io_num = -1, .max_transfer_sz = CHIPLOOP_FRAME_BYTES,
    };
    const spi_device_interface_config_t device = {
        .clock_speed_hz = CHIPLOOP_SPI_CLOCK_HZ, .mode = 0,
        .spics_io_num = CHIPLOOP_PIN_CS, .queue_size = 1,
    };
    ESP_RETURN_ON_ERROR(spi_bus_initialize(CHIPLOOP_SPI_HOST, &bus, SPI_DMA_CH_AUTO), "chiploop", "spi bus");
    ESP_RETURN_ON_ERROR(spi_bus_add_device(CHIPLOOP_SPI_HOST, &device, &chiploop_fpga), "chiploop", "spi device");
    chiploop_tx_dma = heap_caps_calloc(CHIPLOOP_FRAME_BYTES, 1, MALLOC_CAP_DMA);
    chiploop_rx_dma = heap_caps_calloc(CHIPLOOP_FRAME_BYTES, 1, MALLOC_CAP_DMA);
    ESP_RETURN_ON_FALSE(chiploop_tx_dma && chiploop_rx_dma, ESP_ERR_NO_MEM, "chiploop", "DMA buffers");
    chiploop_exchange_lock = xSemaphoreCreateMutex();
    ESP_RETURN_ON_FALSE(chiploop_exchange_lock, ESP_ERR_NO_MEM, "chiploop", "exchange mutex");
    return ESP_OK;
}

esp_err_t chiploop_fpga_exchange(const uint8_t *request, uint8_t *response) {
    ESP_RETURN_ON_FALSE(request && response && chiploop_tx_dma && chiploop_rx_dma && chiploop_exchange_lock, ESP_ERR_INVALID_STATE, "chiploop", "exchange state");
    ESP_RETURN_ON_FALSE(xSemaphoreTake(chiploop_exchange_lock, portMAX_DELAY) == pdTRUE, ESP_ERR_TIMEOUT, "chiploop", "exchange mutex");
    memcpy(chiploop_tx_dma, request, CHIPLOOP_FRAME_BYTES);
    memset(chiploop_rx_dma, 0, CHIPLOOP_FRAME_BYTES);
    spi_transaction_t transaction;
    memset(&transaction, 0, sizeof(transaction));
    transaction.length = CHIPLOOP_FRAME_BYTES * 8;
    transaction.tx_buffer = chiploop_tx_dma;
    transaction.rx_buffer = chiploop_rx_dma;
    esp_err_t status = spi_device_transmit(chiploop_fpga, &transaction);
    // Allow the FPGA core-clock synchronizer to commit the mailbox before a
    // subsequent transaction begins. Response N is visible in frame N+2.
    esp_rom_delay_us(1);
    if (status == ESP_OK) memcpy(response, chiploop_rx_dma, CHIPLOOP_FRAME_BYTES);
    xSemaphoreGive(chiploop_exchange_lock);
    return status;
}

#define REG_VALID_LSB 0
#define REG_WE_LSB 1
#define REG_ADDR_LSB 3
#define REG_ADDR_WIDTH 8
#define REG_WDATA_LSB 11
#define REG_WDATA_WIDTH 32
#define REG_RDATA_LSB 21
#define REG_RDATA_WIDTH 32
#define REG_READY_LSB 53
#define RESPONSE_PADDING_BITS 258

static void frame_set_bits(uint8_t *frame, unsigned lsb, unsigned width,
                           const uint8_t *value, size_t value_bytes) {
    for (unsigned bit = 0; bit < width; ++bit) {
        const unsigned physical = lsb + bit;
        const unsigned byte = CHIPLOOP_FRAME_BYTES - 1u - physical / 8u;
        const uint8_t mask = (uint8_t)(1u << (physical % 8u));
        const uint8_t source = bit / 8u < value_bytes ? value[bit / 8u] : 0u;
        if ((source >> (bit % 8u)) & 1u) frame[byte] |= mask; else frame[byte] &= (uint8_t)~mask;
    }
}

static void frame_get_bits(const uint8_t *frame, unsigned lsb, unsigned width,
                           uint8_t *value, size_t value_bytes) {
    memset(value, 0, value_bytes);
    for (unsigned bit = 0; bit < width; ++bit) {
        const unsigned physical = RESPONSE_PADDING_BITS + lsb + bit;
        const unsigned byte = CHIPLOOP_FRAME_BYTES - 1u - physical / 8u;
        if (bit / 8u < value_bytes)
            value[bit / 8u] |= (uint8_t)(((frame[byte] >> (physical % 8u)) & 1u) << (bit % 8u));
    }
}

static bool frame_get_flag(const uint8_t *frame, unsigned lsb) {
    uint8_t value = 0;
    frame_get_bits(frame, lsb, 1, &value, 1);
    return value != 0;
}

static esp_err_t chiploop_complete_command(uint8_t *request, uint8_t *response) {
    uint8_t idle[CHIPLOOP_FRAME_BYTES] = {0};
    ESP_RETURN_ON_ERROR(chiploop_fpga_exchange(request, response), "chiploop", "command frame");
    ESP_RETURN_ON_ERROR(chiploop_fpga_exchange(idle, response), "chiploop", "pipeline frame 1");
    return chiploop_fpga_exchange(idle, response);
}

esp_err_t chiploop_register_write(const uint8_t *address, size_t address_bytes,
                                  const uint8_t *value, size_t value_bytes) {
    const uint8_t asserted = 1;
    ESP_RETURN_ON_FALSE(address && value, ESP_ERR_INVALID_ARG, "chiploop", "register write buffers");
    ESP_RETURN_ON_FALSE(address_bytes * 8u >= REG_ADDR_WIDTH && value_bytes * 8u >= REG_WDATA_WIDTH,
                        ESP_ERR_INVALID_SIZE, "chiploop", "register write buffer width");
    uint8_t request[CHIPLOOP_FRAME_BYTES] = {0}, response[CHIPLOOP_FRAME_BYTES] = {0};
    frame_set_bits(request, REG_VALID_LSB, 1, &asserted, 1);
    frame_set_bits(request, REG_WE_LSB, 1, &asserted, 1);
    frame_set_bits(request, REG_ADDR_LSB, REG_ADDR_WIDTH, address, address_bytes);
    frame_set_bits(request, REG_WDATA_LSB, REG_WDATA_WIDTH, value, value_bytes);
    ESP_RETURN_ON_ERROR(chiploop_complete_command(request, response), "chiploop", "register write");
    ESP_RETURN_ON_FALSE(frame_get_flag(response, REG_READY_LSB), ESP_ERR_INVALID_RESPONSE, "chiploop", "register not ready");
    return ESP_OK;
}

esp_err_t chiploop_register_read(const uint8_t *address, size_t address_bytes,
                                 uint8_t *value, size_t value_bytes) {
    const uint8_t asserted = 1;
    ESP_RETURN_ON_FALSE(address && value, ESP_ERR_INVALID_ARG, "chiploop", "register read buffers");
    ESP_RETURN_ON_FALSE(address_bytes * 8u >= REG_ADDR_WIDTH && value_bytes * 8u >= REG_RDATA_WIDTH,
                        ESP_ERR_INVALID_SIZE, "chiploop", "register read buffer width");
    uint8_t request[CHIPLOOP_FRAME_BYTES] = {0}, response[CHIPLOOP_FRAME_BYTES] = {0};
    frame_set_bits(request, REG_VALID_LSB, 1, &asserted, 1);
    frame_set_bits(request, REG_ADDR_LSB, REG_ADDR_WIDTH, address, address_bytes);
    ESP_RETURN_ON_ERROR(chiploop_complete_command(request, response), "chiploop", "register read");
    ESP_RETURN_ON_FALSE(frame_get_flag(response, REG_READY_LSB), ESP_ERR_INVALID_RESPONSE, "chiploop", "register not ready");
    frame_get_bits(response, REG_RDATA_LSB, REG_RDATA_WIDTH, value, value_bytes);
    return ESP_OK;
}


void app_main(void) { ESP_ERROR_CHECK(chiploop_fpga_init()); }
