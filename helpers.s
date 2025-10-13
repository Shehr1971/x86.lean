.globl read_int
.globl write_int

read_int:
    push %rbp
    mov %rsp, %rbp

    lea format_in(%rip), %rdi
    lea input_var(%rip), %rsi
    mov $0, %eax
    call scanf

    mov input_var(%rip), %rax

    pop %rbp

    ret

write_int:
    push %rbp
    mov %rsp, %rbp

    mov %rdi, %rsi
    lea format_out(%rip), %rdi
    mov $0, %eax
    call printf

    pop %rbp

    ret

.data
format_in: .string "%d"
format_out: .string "%d\n"
input_var: .long 0
