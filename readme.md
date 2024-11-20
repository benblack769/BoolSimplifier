### Overview

This is a boolean expression parser, simplifier and evaluator. I wrote this long before I knew what git was, but I hope that someone might find this useful or interesting.

expanded_eval.sml: Source, comments, and instructions on useage.
test.bool: File used for input. Modify to use the software

### Compilation

The sml code in expanded_eval.sml can be compiled by either the MLton project or the SML New Jersey.

windows_binary.exe: Binary for windows compile by MLton


### Syntax and usage

It deals with the following syntax

```
<logic> ::= <disj>

<disj> ::= <conj>
<disj> ::= <conj> <disj'>

<disj'> ::= or <disj>

<conj> ::= <atom>
<conj> ::= <atom> <conj'>

<conj'> ::= and <conj>

<atom> ::= not <atom>
<atom> ::= (<logic>)
<atom> ::= True
<atom> ::= False
<atom> ::= <name>
<atom> ::= <variable>

<expr> ::= simplify <logic>
<expr> ::= <logic>

val <variable> = <expr>

print_value <expr>
print_tree <expr>
print_table <expr>
```

You do not need spaces in between parenthesis or equal signs and other words.

Note that it is very flexible in what can be defined as a variable or
a name. For instance you can define a variable as "print_table" or a name
as "and" (and vice versa) and so far I have not been able to contrive any examples of
where this does not work well (otherwise good syntax fails). However, bad syntax
will give very odd errors and do odd things and so you might want to avoid such
practices.

Example File:

```
val oneLook = (lookahead and one)
val tokenize = state_mach and not slow and (simple or not oneLook)
val pars = tokenize and oneLook
val evalu = pars and (interpreter and not slow)
print_value evalu
print_tree evalu
print_table evalu
val simp = simplify evalu
print_value simp
print_tree simp
```

Output:

```
(((state_mach and (not slow and (simple or not (lookahead and one)))) and (lookahead and one)) and (interpreter and not slow))
			state_mach = T
		 and
				slow = F
			 and
					simple = T
				 or
						lookahead = F
					 and
						one = F
	 and
			lookahead = T
		 and
			one = T
 and
		interpreter = T
	 and
		slow = F

```


state_mach|slow|simple|lookahead|one|interpreter|(((state_mach and (not slow and (simple or not (lookahead and one)))) and (lookahead and one)) and (interpreter and not slow))
--- | --- | --- | --- | --- | --- | --- 
T|   T|     T|        T|  T| T|F
F|   T|     T|        T|  T| T|F
T|   F|     T|        T|  T| T|T
F|   F|     T|        T|  T| T|F
T|   T|     F|        T|  T| T|F
F|   T|     F|        T|  T| T|F
T|   F|     F|        T|  T| T|F
F|   F|     F|        T|  T| T|F
T|   T|     T|        F|  T| T|F
F|   T|     T|        F|  T| T|F
T|   F|     T|        F|  T| T|F
F|   F|     T|        F|  T| T|F
T|   T|     F|        F|  T| T|F
F|   T|     F|        F|  T| T|F
T|   F|     F|        F|  T| T|F
F|   F|     F|        F|  T| T|F
T|   T|     T|        T|  F| T|F
F|   T|     T|        T|  F| T|F
T|   F|     T|        T|  F| T|F
F|   F|     T|        T|  F| T|F
T|   T|     F|        T|  F| T|F
F|   T|     F|        T|  F| T|F
T|   F|     F|        T|  F| T|F
F|   F|     F|        T|  F| T|F
T|   T|     T|        F|  F| T|F
F|   T|     T|        F|  F| T|F
T|   F|     T|        F|  F| T|F
F|   F|     T|        F|  F| T|F
T|   T|     F|        F|  F| T|F
F|   T|     F|        F|  F| T|F
T|   F|     F|        F|  F| T|F
F|   F|     F|        F|  F| T|F
T|   T|     T|        T|  T| F|F
F|   T|     T|        T|  T| F|F
T|   F|     T|        T|  T| F|F
F|   F|     T|        T|  T| F|F
T|   T|     F|        T|  T| F|F
F|   T|     F|        T|  T| F|F
T|   F|     F|        T|  T| F|F
F|   F|     F|        T|  T| F|F
T|   T|     T|        F|  T| F|F
F|   T|     T|        F|  T| F|F
T|   F|     T|        F|  T| F|F
F|   F|     T|        F|  T| F|F
T|   T|     F|        F|  T| F|F
F|   T|     F|        F|  T| F|F
T|   F|     F|        F|  T| F|F
F|   F|     F|        F|  T| F|F
T|   T|     T|        T|  F| F|F
F|   T|     T|        T|  F| F|F
T|   F|     T|        T|  F| F|F
F|   F|     T|        T|  F| F|F
T|   T|     F|        T|  F| F|F
F|   T|     F|        T|  F| F|F
T|   F|     F|        T|  F| F|F
F|   F|     F|        T|  F| F|F
T|   T|     T|        F|  F| F|F
F|   T|     T|        F|  F| F|F
T|   F|     T|        F|  F| F|F
F|   F|     T|        F|  F| F|F
T|   T|     F|        F|  F| F|F
F|   T|     F|        F|  F| F|F
T|   F|     F|        F|  F| F|F
F|   F|     F|        F|  F| F|F


```
(interpreter and (one and (lookahead and (simple and (not slow and state_mach)))))
	interpreter = T
 and
		one = T
	 and
			lookahead = T
		 and
				simple = T
			 and
					slow = F
				 and
					state_mach = T
```

Note: The simplifier is of O(n+1)! asymtotic complexity (due to a bug, it really should be
O(n!)) where n is the number of words in the expression, so it really is incredibly
inefficient, and really cannot handle more than 7 variables, although 8 works if you
are patient (several minutes).