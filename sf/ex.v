Require Import Nat.
Require Import List.
Import ListNotations.

(* CAPITULO 1 *)

Theorem plus_id_exercise:
  forall n m o: nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n' m' o'.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  destruct p as [ | n'].
  - simpl. reflexivity.
  - simpl.
    (* Search (_ * 1 = _). *)
    rewrite -> PeanoNat.Nat.mul_1_r.
    reflexivity.
Qed.

Search (_ * 1 = _).

Search nat.

Compute (PeanoNat.Nat.two) + (PeanoNat.Nat.two).

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof. Admitted.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof. Admitted.

(** **)

(* CAPITULO 2 *)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [ | n' HipoteseIndutiva ].
  - simpl. reflexivity.
  - simpl. rewrite -> HipoteseIndutiva. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n' m'.
  induction n' as [ | n'' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n' m' p'.
  induction n' as [ | n'' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    reflexivity.
Qed.

(* CAPITULO 3 *)

Theorem app_assoc : forall l1 l2 l3 : list nat,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.




