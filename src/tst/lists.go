package main
import "fmt"

type List struct {
	head int
	tail *List
}


func sum(l List) int {
	if (l.tail == nil) {
		return l.head
	}
	return (l.head + sum(*l.tail))
}


func main() {
	var l List;
	l.tail := nil;
	l.head :=3;
	fmt.Print(sum(l));
}
