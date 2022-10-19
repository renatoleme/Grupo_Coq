# Programação no Coq

> Rudimentos de programação funcional

Gallina é uma linguagem de programação puramente funcional. Em outras palavras, ela é fundada em dois princípios básicos: 

1. **Imutabilidade dos dados:** não existe efeito colateral, o mapeamento input/output é perfeito;
2. **Primazia das funções**: toda função possui um tipo e, como tal, é um elemento que pode ser passado como parâmetro para outras funções.

Um programa no Coq é uma função. Uma função é uma regra que especifica a transformação de um objeto de tipo X em um objeto de tipo Y (possivelmente igual a X). 

## Currying

Você deve ter notado que, ao checar o tipo de uma função que recebe múltiplos parâmetros, a resposta é sempre

```
tipo1 -> tipo2 -> ... -> tipon
```

Isso se dá através de um processo conhecido como *currying*, que transforma $f (a, b)$ em $f(a) b$. Considere a função $f$ a seguir:

$$
\begin{align}
f &: (X_0 * X_1 * \cdots * X_n) \rightarrow Y \\
c(f)  &: (X_0 * X_1 * \cdots) \rightarrow (X_n \rightarrow Y)  \\
  &: X_0 \rightarrow ( X_1 \rightarrow \cdots \rightarrow (X_n \rightarrow Y))  
\end{align}
$$

Note que a associatividade do operador produto cartesiano $*$ é inversa a associatividade do operador $\rightarrow$.

> **Curiosidade**
> O operador $\rightarrow$ é apenas uma notação (*syntactic sugar*) para 
> ```coq
> forall _ : A, B
> ```

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
> O que aconteceria se o tipo bool fosse definido da seguinte maneira?
>```coq
>Inductive bool : Type :=
>| false
>| true.
>```
> Dica: "Logic is not a body of doctrine, but a mirror-image of the world. Logic is transcendental." (TLP, 6.13)

> **Exercício**
> Defina os operadores usuais da lógica clássica utilizando o tipo bool e o *if-then-else*.

## Programando com os naturais

## Programando com listas
