.text
.globl _start
_start:
    la   s0, fib_data        # ponteiro para RAM
    li   s1, 0x00000104      # endereço MMIO dos LEDs

    lw   t0, 0(s0)           # fib(0)
    lw   t1, 4(s0)           # fib(1)

loop:
    add  t2, t0, t1          # fib(n)
    sw   t2, 8(s0)           # guarda na RAM
    sw   t2, 0(s1)           # escreve nos LEDs
    mv   t0, t1
    mv   t1, t2
    addi s0, s0, 4           # avança vetor

    j loop                   # 7 instruções por iteração

.data
.align 2

fib_data:
    .word 0
    .word 1
    .space 64              # espaço para a sequência

fib_out:
    .word 0

