#!/usr/bin/env bash
# Rebuilds getpid_loop_x86_64 (no libc; gcc + binutils only).
set -euo pipefail
cd "$(dirname "$0")"
gcc -O2 -fPIE -ffreestanding -fno-builtin -fno-stack-protector \
    -fcf-protection=none -fno-asynchronous-unwind-tables -Wall -Wextra \
    -static -no-pie -nostdlib \
    -Wl,-Ttext-segment=0x8000001000 -Wl,-z,noexecstack -Wl,--build-id=none \
    -o getpid_loop_x86_64 getpid_loop_x86_64.c
strip --strip-all getpid_loop_x86_64
