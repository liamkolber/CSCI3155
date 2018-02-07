#2a
- pi at line 4 is bound at line 3 because it is within the scope starting at line 2 therefore line 3's binding takes precendent over the binding in line 1.
- pi at line 7 is bound at line 1 because it is in the global scope like the pi binding at line 1.

#2b
- x at line 3 is bound at line 2 because it is within the scope beginning at line 2 (the function parameters).
- x at lines 6 and 10 are bound to line 5 because they are within the scope started by the "case."
- x at line 13 is bound to line 1 because it is within the globa scope.

#3
This is well typed and with type int.

x: int 		3: int 		1: int 		a: int 		b: int

(x, 3): int --> (1, (x, 3)): int
	--> (a, b): int   &   (b, 1): int   &   (b, a+2): int