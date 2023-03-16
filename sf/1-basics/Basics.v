(* 

  Material para o encontro do
  dia 17/03/2023. 
  
  Unicamp. GLM/Grupo_Coq. 

  Autor: Renato Reis Leme
  Web: https://renatoleme.github.io/
  
  São Paulo, 16 de março de 2023.
*)

Require Import String.

Inductive string_or_nat := 
| String : string -> string_or_nat
| Nat : nat -> string_or_nat.

Check String "Hello World!".
Check Nat 23.

(* Record type (each of) *)

Inductive nat_string_pair :=
| Pair : (nat * string) -> nat_string_pair.

Open Scope string_scope.

Check Pair (23 , "Hello World!").

Close Scope string_scope.

(**)

Inductive dia : Type := 
| Segunda
| Terca
| Quarta
| Quinta
| Sexta
| Sabado
| Domingo.

Check Segunda.
Check Domingo.
Check Sexta.

Definition proximo_dia_util 
  (d : dia) : dia :=
  match d with
  | Segunda => Terca
  | Terca => Quarta
  | Quarta => Quinta
  | Quinta => Sexta
  | Sexta => Segunda
  | Sabado => Segunda
  | Domingo => Segunda
  end.
  
Compute proximo_dia_util 
(proximo_dia_util Quarta).

Example teste_proximo_dia_util :
  (proximo_dia_util 
  (proximo_dia_util Terca)) = Quinta.
Proof.
  simpl. reflexivity.
Qed.

(**)

Inductive bool : Type := true | false.

Definition negb (b : bool) : bool :=
  match b with
    true => false
  | false => true
  end.

Definition andb (a b : bool) : bool :=
  match a with
    true => b
  | false => false
  end.

Definition orb (a b : bool) : bool :=
  match a with
    true => true
  | false => b
  end.
  
Example test_orb1: 
(orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: 
(orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: 
(orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: 
(orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb_notation : 
false || true || false || 
false || false = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool :=
  if b then false
  else true.

Definition andb' (a b : bool) : bool :=
  if a then b
  else false.

Definition orb' (a b : bool) : bool :=
  if a then true
  else b.
  
Check true.
Check (negb true) : bool.

(**)

Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
  
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.