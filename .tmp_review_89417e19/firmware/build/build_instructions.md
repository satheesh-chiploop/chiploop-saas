<!-- ASSUMPTION: Build executed inside the ChipLoop runtime image -->
<!-- ASSUMPTION: Cargo and the requested target toolchain are already installed -->

# Build Instructions

## Build ELF

cargo build --release --target x86_64-unknown-linux-gnu

## Expected Cargo Output

target/x86_64-unknown-linux-gnu/release/firmware_app

## Optional Canonical ELF Copy

mkdir -p firmware/build/target/x86_64-unknown-linux-gnu/release
cp target/x86_64-unknown-linux-gnu/release/firmware_app firmware/build/target/x86_64-unknown-linux-gnu/release/firmware_app.elf

## Validate ELF Exists

ls firmware/build/target/x86_64-unknown-linux-gnu/release/firmware_app.elf
