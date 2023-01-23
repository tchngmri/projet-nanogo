	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	movq $S_1, %rdi
	call print_string

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
S_1:
	.string "Hello World"
