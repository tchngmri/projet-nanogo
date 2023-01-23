	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_somme:
	pushq %rbp
	movq %rsp, %rbp
	pushq $0
	movq 24(%rbp), %rdi
	pushq %rdi
	movq 16(%rbp), %rdi
	movq %rdi, %rax
	popq %rdi
	addq %rax, %rdi
	movq %rdi, -8(%rbp)
	movq -8(%rbp), %rdi
	jmp E_somme
	popq %rdi
E_somme:
	movq %rbp, %rsp
	popq %rbp
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	pushq $0
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
