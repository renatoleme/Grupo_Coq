(* Provando teoremas no Coq. Introdução. *)

Require Import Arith.
Require Import Bool.

(*
  Nesta seção, veremos três "estilos" de prova no Coq.

  (1) Prova por Simplificação;
  (2) Prova por Reescrita;
  (3) Prova por Análise de Caso.

  Iremos nos habituar ao ambiente prova, analisando detalhadamente cada passo.
*)

(* Prova por Simplificação *)

Theorem plus_0_n : forall n, 0 + n = n.
Proof.
  intros n'.
  simpl.
  reflexivity.
Qed.

(* reflexivity já faz o trabalho do simpl. *)

Theorem plus_0_n' : forall n, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

(*
The keywords intros, simpl, and reflexivity are examples of tactics. A tactic is a command that is used between Proof and Qed to guide the process of checking some claim we are making. We will see several more tactics in the rest of this chapter and many more in future chapters.
*)

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl.
  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl.
  reflexivity.
Qed.

Theorem teorema_falho : forall n : nat, n + 1 = n.
Proof.
  intros n.
  simpl.
Abort.

(*
It is worth stepping through these proofs to observe how the context and the goal change.
*)

(* Prova por Reescrita *)

(* 
Instead of making a universal claim about all numbers n and m, ... [the following theorem] talks about a more specialized property that only holds when n = m. *)
Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite <- H.
  (* rewrite <- H. *)
  reflexivity.
Qed.

(* Exercício *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

(*Be careful (...): every time you say Admitted you are leaving a door open for total nonsense to enter Coq's nice, rigorous, formally checked world!*)

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* Exercício *)

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  Check mult_n_Sm.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(* Prova por Análise de Caso *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. simpl.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*
The annotation "as [| n']" is called an intro pattern. It tells Coq what variable names to introduce in each subgoal. In general, what goes between the square brackets is a list of lists of names, separated by |. In this case, the first component is empty, since the O constructor is nullary (it doesn't have any arguments). The second component gives a single name, n', since S is a unary constructor.
*)

(*
The destruct tactic can be used with any inductively defined datatype. For example, we use it next to prove that boolean negation is involutive -- i.e., that negation is its own inverse.
*)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. simpl. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

(* 
Duas boas práticas:

(1) Prefira linhas de no máximo 80 caracteres;
(2) Dê nomes intuitivos às variáveis.

*)

Theorem andb_commutative : forall b c : bool, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb. destruct c eqn:Ec. reflexivity. reflexivity. destruct c eqn:Ec. reflexivity. reflexivity.
Qed.

Theorem andb_commutative' : forall b c : bool, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* Exercício *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
Admitted.

(* Uma convenção: intros + destruct. *)

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercício *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
Admitted.

