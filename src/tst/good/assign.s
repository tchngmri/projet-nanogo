	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	pushq $0
	movq $2, %rdi
	movq %rdi, -8(%rbp)
	movq -8(%rbp), %rdi
	call print_int
	popq %rdi
E_main:
	movq %rbp, %rsp
	popq %rbp
	ret

print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_string: 
	      movq %rdi, %rsi
	      movq $S_string, %rdi
	      xorq %rax, %rax
	      call printf
	      ret
	.data
S_int:
	.string "%ld"
S_string:
	.string "%s"
