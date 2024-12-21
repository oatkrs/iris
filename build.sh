#!/bin/bash
set -e

# Check required tools
for cmd in nasm gcc; do
    if ! command -v $cmd &> /dev/null; then
        echo "Error: $cmd not installed"
        exit 1
    fi
done

echo "[+] Compiling iris.c..."
gcc -o iris iris.c -lcapstone -lkeystone

if [ ! -f sample.asm ]; then
    echo "Error: sample.asm not found."
    exit 1
fi

echo "[+] Running IRIS on sample.asm..."
./iris sample.asm output.asm

echo "[+] Assembling output.asm with NASM..."
nasm -f elf64 output.asm -o output.o

echo "[+] Linking output.o to final executable..."
gcc -no-pie -nostartfiles output.o -o output

echo "[+] Running final executable:"
./output

echo "[+] Process completed successfully."
