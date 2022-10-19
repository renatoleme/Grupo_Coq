# Programação no Coq

> Rudimentos de programação funcional

Gallina é uma linguagem de programação puramente funcional. Em outras palavras, ela é fundada em dois princípios básicos: 

1. **Imutabilidade dos dados:** não existe efeito colateral, o mapeamento input/output é perfeito;
2. **Primazia das funções**: toda função possui um tipo e, como tal, é um elemento que pode ser passado como parâmetro para outras funções.

Um programa no Coq é uma função. Uma função é uma regra que especifica a transformação de um objeto de tipo X em um objeto de tipo Y (possivelmente igual a X). 

Através de um processo conhecido como *currying*, essa definição pode ser generalizada. Considere a função $f$ a seguir:

$$
\begin{align}
f &: X_0 \rightarrow X_1 \rightarrow \cdots \rightarrow X_n \\
  &: X_0 \rightarrow (X_1 \rightarrow ... \rightarrow X_{n-1} \rightarrow X_n)  \\
  &: X_0 \rightarrow (X_1 \rightarrow ... \rightarrow (X_{n-1} \rightarrow X_n))
\end{align}
$$

Neste exemplo, *f* é uma regra que transforma do tipo $X_0$ no tipo $f_0 : X_1 \rightarrow ... \rightarrow X_{n-1} \rightarrow X_n$. O tipo $f_0$, por sua vez, é uma regra que transforma do tipo $X_1$ no tipo $f_1 : ... \rightarrow (X_{n-1} \rightarrow X_n)$, e assim por diante. Na prática, o *currying* transforma uma função de $n$ valores de entrada em uma série de funções que recebem, cada uma, uma única entrada.

## Funções anônimas e nomeadas

No Coq, uma função pode ser anônima ou nomeada. Já vimos alguns exemplos do primeiro tipo: são funções definidas através da abstração *fun*.

```coq
Check (fun n => n = n).
: nat -> Prop
```

Funções nomeadas, por sua vez, podem ser definidas de duas maneiras:

1. Definition;
2. Fixpoint.

### Definition

### Fixpoint

## O tipo **bool** e as condicionais

Se existisse uma hierarquia, o **bool** seria o terceiro tipo mais simples possível (perdendo apenas para o tipo vazio e o tipo unitário). Apesar disso, como se sabe, o tipo **bool** é extremamente útil. 

Sendo capaz de assumir apenas um valor dentre dois (usualmente chamados de *true* e *false*) por vez, com ele podemos espelhar perfeitamente a lógica clássica.

```coq
Inductive bool : Type :=
| true
| false.
```

Para isso, basta a adição de um novo operador em nossa linguagem: *if-then-else*. 

```coq
if true then (* faça isso *)
else (* faça aquilo *)
```

No Coq, a convenção estabelece que a avaliação do *if* será **verdadeira** sempre que o valor assumido pela variável avaliada for igual ao primeiro valor do tipo da variável. Em qualquer outro caso, a avaliação é **falsa** e o interpretador executa a cláusula do *else*.

> **Exercício**
> O que aconteceria se o tipo bool fosse definido da seguinte maneira:
>```coq
>Inductive bool : Type :=
>| false
>| true.
>```
> ?

> **Exercício**
> Defina os operadores usuais da lógica clássica utilizando o tipo bool e o *if-then-else*.

## Programando com os naturais

## Programando com listas
