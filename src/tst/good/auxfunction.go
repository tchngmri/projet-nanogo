package main
import "fmt"

func somme(x int, y int) int {
	total := 0;
	total = x + y;
	return total
}

func main() {
	sum := somme(20, 30);
	fmt.Print(sum)
}
