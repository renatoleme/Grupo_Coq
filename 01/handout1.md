# Coq

O sistema do Coq oferece uma linguagem para

1) Lidar com fórmulas.
2) Checar se uma fórmula é bem-formada.
3) Provar.

**Exemplo**

Queremos definir a fórmula dos números naturais.

```
0, 1, 2, 3 ...
```

## Linguagem semi-formalizada

Um número natural **n** é um objeto do tipo N tal que


```
(1) n é igual a 0; ou
(2) n é igual a succ (m do tipo N)
```
onde **succ** é uma função N $\rightarrow$ N

+ 0 = 0
+ 1 = succ 0
+ 2 = succ (succ 0)
+ 3 = succ (succ (succ 0))
+ ...

## Linguagem formalizada

O nome da linguagem do Coq é... [Gallina](https://coq.github.io/doc/v8.9/refman/language/gallina-specification-language.html). Nessa linguagem, podemos redefinir o tipo acima da seguinte maneira.

```coq
Inductive nat : Type :=
| O
| S (n : nat).
```

E os números então se tornam

+ 0 = O
+ 1 = S O
+ 2 = S (S O)
+ 3 = S (S (S O))
+ ...

Uma das vantagens em definir o tipo em uma linguagem formalizada é que podemos checar, programaticamente, se uma fórmula é bem formada.

# Check

**Propósito:** checar se uma fórmula é bem formada.

1. **O** é bem formado;
2. **S O** é bem formado;
3. **S (S O)** é bem formado;
4. **(S S) O** não é bem formado.

O comando *Check X* verifica se a fórmula *X* é bem formada; se for bem formada, o comando retorna o tipo da fórmula.

"Checar" é diferente de provar: uma fórmula pode ser bem formada e mesmo assim ser falsa.

Por exemplo: **False**.

```coq
Check False.
> False : Prop
```

Outros exemplos.

```coq
Check True.
> True : Prop
```

```coq
Check 3.
> 3 : nat
```

```coq
Check (3+4).
> 3 + 4 : nat
```

```coq
Check (3=5).
> 3 = 5 : Prop
```

```coq
Check ((3=5)/\True).
> 3 = 5 /\ True : Prop
```

```coq
Check nat -> Prop.
> nat -> Prop : Type
```

Exemplo de fórmula do tipo nat $\rightarrow$ Prop

```coq
fun (n : nat) => n = n
     : nat -> Propss
```

A notação **A : B** pode significar que a expressão **A** tem o tipo **B** ou que **A** é uma prova de **B**.


