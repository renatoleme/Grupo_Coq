(**  
  Exercícios

  1) Theorem ex1 : forall P Q, P /\ Q -> P.
  2) Theorem ex2 : forall P Q, P /\ Q -> Q.
  3) Theorem ex3 : forall P Q, (P -> Q) -> P -> Q.
  4) Theorem ex4 : forall P Q R, (P \/ Q) -> (P -> R) -> (Q -> R) -> R.

**)

Theorem ex1 : forall P Q, P /\ Q -> P.
Proof.
  intros. destruct H as [H1 H2]. apply H1.
Qed.

Theorem ex2 : forall P Q, P /\ Q -> Q.
Proof.
  intros. destruct H as [H1 H2]. apply H2.
Qed.

Theorem ex3 : forall P Q, (P -> Q) /\ P -> Q.
Proof.
(* Prova aqui *)
Admitted.

Theorem ex4 : forall P Q R, (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
(* Prova aqui *)
Admitted.