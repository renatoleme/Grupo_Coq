# Tabela de conteúdo

- [Tabela de conteúdo](#tabela-de-conteúdo)
- [Notas](#notas)
- [Exercícios](#exercícios)
  - [Exercícios básicos](#exercícios-básicos)
    - [(:star:) nandb](#star-nandb)
    - [(:star:) andb3](#star-andb3)
    - [(:star:) factorial](#star-factorial)
    - [(:star:) ltb](#star-ltb)
    - [(:star:) plus\_id\_exercise](#star-plus_id_exercise)
    - [(:star:) mult\_n\_1](#star-mult_n_1)
    - [(:star::star:) andb\_true\_elim2](#starstar-andb_true_elim2)
    - [(:star:) zero\_nbeq\_plus\_1](#star-zero_nbeq_plus_1)
  - [Exercícios adicionais](#exercícios-adicionais)
    - [(:star:) identity\_fn\_applied\_twice](#star-identity_fn_applied_twice)
    - [(:star:) negation\_fn\_applied\_twice](#star-negation_fn_applied_twice)
    - [(:star::star::star:) andb\_eq\_orb](#starstarstar-andb_eq_orb)
    - [(:star::star::star:) binary](#starstarstar-binary)

# Notas

> If a procedure or method has no side effects, then (ignoring efficiency) all we need to understand about it is how it maps inputs to outputs -- that is, we can think of it as just a concrete method for computing a mathematical function. [(Introduction, SF 1)](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html)

> The other sense in which functional programming is "functional" is that it emphasizes the use of functions as **first-class values** -- i.e., values that can be passed as arguments to other functions, returned as results, included in data structures, etc. The recognition that functions can be treated as data gives rise to a host of useful and powerful programming idioms. [(Introduction, SF 1)](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html)

Dentre as features comuns a linguagens funcionais, destacam-se

1. algebraic data types;
2. pattern matching;
3. polymorphic type systems.

# Exercícios

Os exercícios a seguir foram extraídos de [Software Foundations, Vol. 1, Cap. 1](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html).

## Exercícios básicos

### (:star:) nandb

> Remove "Admitted." and complete the definition of the following function; then make sure that the Example assertions below can each be verified by Coq. (...) The function should return true if either or both of its inputs are false.
>>Hint: if simpl will not simplify the goal in your proof, it's probably because you defined nandb without using a match expression. Try a different definition of nandb, or just skip over simpl and go directly to reflexivity. We'll explain this phenomenon later in the chapter.

```coq
Definition nandb (b1:bool) (b2:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nandb1: (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.
```

### (:star:) andb3

> Do the same for the andb3 function below. This function should return true when all of its inputs are true, and false otherwise.

```coq
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32: (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33: (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34: (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
```

### (:star:) factorial

> Recall the standard mathematical factorial function:
```       
factorial(0)  =  1
factorial(n)  =  n * factorial(n-1)     (if n>0)
```
>Translate this into Coq.
Make sure you put a := between the header we've given you and your definition. If you see an error like "The reference factorial was not found in the current environment," it means you've forgotten the :=.

```coq
Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
```

### (:star:) ltb

> The ltb function tests natural numbers for less-than, yielding a boolean. Instead of making up a new Fixpoint for this one, define it in terms of a previously defined function. (It can be done with just one previously defined function, but you can use two if you want.)

```coq
Definition ltb (n m : nat) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_ltb2: (ltb 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_ltb3: (ltb 4 2) = false.
(* FILL IN HERE *) Admitted.
```

### (:star:) plus_id_exercise

> Remove "Admitted." and fill in the proof.

```coq
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
```

### (:star:) mult_n_1

> Use those two lemmas about multiplication that we just checked to prove the following theorem. Hint: recall that 1 is S O.

```coq
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  (* FILL IN HERE *) Admitted.
```

### (:star::star:) andb_true_elim2

> Prove the following claim, marking cases (and subcases) with bullets when you use destruct.
>>Hint: You will eventually need to destruct both Booleans, as in the theorems above. But, delay introducing the hypothesis until after you have an opportunity to simplify it.
>
>>Hint 2: When you reach contradiction in the hypotheses, focus on how to rewrite with that contradiction.

```coq
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
```

### (:star:) zero_nbeq_plus_1

```coq
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
```

## Exercícios adicionais

### (:star:) identity_fn_applied_twice

> Use the tactics you have learned so far to prove the following  theorem about boolean functions.

```coq
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.
```

### (:star:) negation_fn_applied_twice

> Now state and prove a theorem negation_fn_applied_twice similar to the previous one but where the second hypothesis says that the function f has the property that f x = negb x.

```coq
(* FILL IN HERE *)
```

### (:star::star::star:) andb_eq_orb

> Prove the following theorem. (Hint: This one can be a bit tricky, depending on how you approach it. You will probably need both destruct and rewrite, but destructing everything in sight is not the best way.)

```coq
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
```
### (:star::star::star:) binary

> We can generalize our unary representation of natural numbers to the more efficient binary representation by treating a binary number as a sequence of constructors B0 and B1 (representing 0s and 1s), terminated by a Z. For comparison, in the unary representation, a number is a sequence of S constructors terminated by an O.
For example:

```
        decimal               binary                          unary
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))
```

> Note that the low-order bit is on the left and the high-order bit is on the right -- the opposite of the way binary numbers are usually written. This choice makes them easier to manipulate.

```coq
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
```

> Complete the definitions below of an increment function incr for binary numbers, and a function bin_to_nat to convert binary numbers to unary numbers.

```coq
Fixpoint incr (m:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Fixpoint bin_to_nat (m:bin) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
```

> The following "unit tests" of your increment and binary-to-unary functions should pass after you have defined those functions correctly. Of course, unit tests don't fully demonstrate the correctness of your functions! We'll return to that thought at the end of the next chapter.

```coq
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
(* FILL IN HERE *) Admitted.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
(* FILL IN HERE *) Admitted.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
(* FILL IN HERE *) Admitted.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
(* FILL IN HERE *) Admitted.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
(* FILL IN HERE *) Admitted.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
(* FILL IN HERE *) Admitted.
```