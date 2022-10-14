# Coq

Uma linguagem para

1) Lidar com formulas.
2) Checar se uma fórmula é bem-formada.
3) Provar.

Exemplo:

Queremos definir o tipo dos números naturais.

0, 1, 2, 3 ...

## Linguagem semi-formalizada

Um número natural X é um objeto do tipo N, onde

N : Tipo

X ou é 0
ou é succ (m : N)

onde succ é uma função N -> N

0 = 0
1 = succ 0
2 = succ (succ 0)
3 = succ (succ (succ 0))
...

## Linguagem formalizada

Inductive nat : Type :=
| O
| S (n : nat).

# Check

Propósito: checa se uma fórmula é bem formada.

O comando "Check X" verifica se a fórmula X é bem formada.

"Checar" é diferente de provar.

Uma fórmula pode ser bem formada e mesmo assim ser falsa.

Por exemplo: False.

Check False.
> False : Prop.

Exemplo de fórmula do tipo nat -> Prop

fun n : nat => n = n
     : nat -> Prop





