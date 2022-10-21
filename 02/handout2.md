# Programação no Coq

> Rudimentos de programação funcional

Gallina é uma linguagem de programação puramente funcional. Em outras palavras, ela é fundada em dois princípios básicos: 

1. **Imutabilidade dos dados:** não existe efeito colateral, i.e, o mapeamento input/output é perfeito, garantindo que o resultado do output dependa exclusivamente do valor dos parâmetros passados como input;
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
curry(f)  &= (X_0 * X_1 * \cdots) \rightarrow (X_n \rightarrow Y)  \\
  &= (X_0 * X_1) \rightarrow (\cdots \rightarrow (X_n \rightarrow Y)) \\
    &= X_0 \rightarrow ( X_1 \rightarrow (\cdots \rightarrow (X_n \rightarrow Y)))  
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

## Programando com os booleanos

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

```coq
Definition negb (a : bool) := if a then false else true.
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

## O estilo *match-pattern*

Seja *type1* um tipo definido como

```coq
Inductive type1 :=
| A : X -> Y -> ... -> Z -> type1.
```
O **match** de um termo de tipo X mapeia cada possível valor de X a uma ação. Exemplo:

```coq
match (term : type1) with
| A x y .. z => ...
end.
```

Além disso, o **match** permite o uso de padrões mais complexos. Exemplo:

```coq
Definition getFirstTwo (l : list nat) :=
match l with
| nil => nil
| h1::h2::tl => h1::h2::nil
| h::tl => h::tl
end.
```

Nesse exemplo, construímos um padrão extra para o tipo da lista: um padrão que captura os dois primeiros elementos de uma lista de naturais qualquer.

## Programando com os naturais

Ao contrário do tipo **bool**, existem infinitos objetos do tipo **nat**. Para definí-lo, utilizamos recursão.

```coq
Inductive nat :=
| O
| S (n : nat).
```

Podemos pensar o tipo **nat** como um conjunto infinito que é gerado indutivamente. Sobre os elementos desse conjunto, como usual, definimos operações como soma, subtração (restrita), multiplicação e exponenciação. 

```coq
Fixpoint plus (a b : nat) :=
match a with
| O => b
| S n => S (plus n b) 
end.
```

> **Exercício**
> Tente definir *plus* sem utilizar recursão. Procure entender porque não é possível.

> **Exercício**
> Defina os demais operadores aritméticos usuais.

Números naturais são empregados em contextos de contagem e, em geral, em contextos (discretos) nos quais a ordem é importante.

## Programando com listas

A definição recursiva usual de lista diz que uma lista de *X* é

1. vazia; ou
2. uma construção contendo um elemento de tipo *X* (cabeça) e uma lista de *X* (cauda);

Assim como os naturais, o tipo das listas é um dos tipos *built-in* do Coq. Para utilizá-lo, adicione no início do seu código

```coq
Require Import List. (* Importa as definições e teoremas *)
Import ListNotations. (* Importa as notações *)
```

As listas, sendo uma estrutura ordenada de objetos, são muito versáteis. Nesse agrupamento, os elementos estabelecem uma relação de ordem entre si, de modo que o primeiro elemento é sempre a cabeça, e o último elemento é a cabeça da última cauda.

Por exemplo, considere a seguinte função que recebe uma lista de booleanos e retorna **true** se, e somente se, todos os elementos da lista são **true**.

```coq
Fixpoint all_true (l : list bool) :=
match l with
| nil => true
| h::tl => if h then all_true tl else false
end.

Definition exists_false (l : list bool) := negb (all_true l).
```


```coq
Definition lista_b := [true;false;false;true].
```


```coq
Compute all_true lista_b.
= false
: bool
Compute exists_false lista_b.
= true
: bool
```

### Anexação

Para adicionar (anexar) um elemento em uma lista, utiliza-se o operador **_ :: _**.

Seja **a** um elemento de tipo *X* e **L** uma lista de elementos de tipo *X*, então

```
a::L = [a;..L]
```

#### Exemplo

```coq
Check nil.
: list ?T
```

```coq
Check 1::2::3::4::nil.
: list nat
```

### Concatenação

A operação de *concatenação* corresponde a operação de "grudar" um elemento de tipo *X* em outro elemento do tipo *Y*. Por exemplo, a concatenação da string "Hello, " com a string "World!" resulta em "Hello, World!".

Para concatenar uma lista com outra utiliza-se o operador **_ ++ _**. 

Sejam **A** e **B** duas listas, então

```
A ++ B = [..A;..B]
```

#### Exemplo

```coq
Compute (1::2::nil) ++ (3::4::nil).
= [1;2;3;4]
: list nat
```

### Map

> Segundo aspecto característico de uma linguagem puramente funcional.

Uma das funções de ordem superior mais conhecidas (e úteis) é o **map**. Com essa função, você transforma cada elemento de uma lista de acordo com a regra passada como parâmetro.

#### Exemplo

```coq
Compute map negb [true;false;true;false].
= [false; true; false; true]
: list bool
```

Assim como definimos, acima, *exists_false* em termos do *all_true*, utilizando o **map** podemos definir, também, uma função *all_false*:

```coq
Definition all_false (l : list bool) := all_true (map negb l).
```

# Exercícios (coq-hurry)

>**Exercise on lists, map, and app** Define a function that takes as input a number n and
returns a list with n elements, from 0 to n − 1.

>**Exercise on sorting** Define a function that takes a list as input and returns true when
it has less than 2 elements or when the first element is smaller than or equal to
the second one. Then define a function that takes a list as input and returns true
exactly when this list is sorted (Hint: when the list has at least two elements, the
first element must be smaller than the second element and the tail must be sorted,
use the first function to write the second one).

>**Exercise on counting** Knowing that the Coq system provides a function Nat.eqb to
compare two natural numbers (Nat.eqb n p returns true exactly when n = p),
define a function count list that takes a natural number and a list and returns
the number of times the natural number occurs in the list.