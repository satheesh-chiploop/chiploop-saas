<!-- ASSUMPTION: Build executed inside the ChipLoop runtime image -->
<!-- Cargo/rustup are runtime-image requirements; standard targets are preinstalled and other explicitly selected standard targets are provisioned before retry. -->

# Build Instructions

## Build ELF

cargo build --release --target riscv32imc-unknown-none-elf

## Expected Cargo Output

target/riscv32imc-unknown-none-elf/release/firmware_app

## Optional Canonical ELF Copy

mkdir -p firmware/build/target/riscv32imc-unknown-none-elf/release
cp target/riscv32imc-unknown-none-elf/release/firmware_app firmware/build/target/riscv32imc-unknown-none-elf/release/firmware_app.elf

## Validate ELF Exists

ls firmware/build/target/riscv32imc-unknown-none-elf/release/firmware_app.elf
