<!-- ASSUMPTION: Build executed inside the ChipLoop runtime image -->
<!-- ASSUMPTION: Cargo and the requested target toolchain are already installed -->

# Build Instructions

## Build ELF

cargo build --release --target rv32imc-unknown-none-elf

## Expected Cargo Output

target/rv32imc-unknown-none-elf/release/firmware_app

## Optional Canonical ELF Copy

mkdir -p firmware/build/target/rv32imc-unknown-none-elf/release
cp target/rv32imc-unknown-none-elf/release/firmware_app firmware/build/target/rv32imc-unknown-none-elf/release/firmware_app.elf

## Validate ELF Exists

ls firmware/build/target/rv32imc-unknown-none-elf/release/firmware_app.elf
