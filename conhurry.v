(** A diretriz Check **)

Set Printing Parentheses.

Theorem or_left: forall P Q : Prop, P -> P \/ Q.
Proof.
  intros. left. apply H.
Qed.

Theorem or_right: forall P Q : Prop, Q -> P \/ Q.
Proof.
  intros. right. apply H.
Qed.

Theorem elim_or: forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (P \/ Q) -> R.
Proof.
  intros.
  destruct H1.
  - apply H in H1. apply H1.
  - apply H0 in H1. apply H1.
Qed.

Check forall x, x >= 2.

(* S x < 3 -> x < 3 *)
(*
Lemma lema1 : forall x, x < 3 \/ (exists y, x = y + 3).
Proof.
  intros.
  induction x.
  - left . auto.
  - destruct IHx.
    assert (Hc1 : S x < 3 -> (x < 3) \/ (x >= 3)).
    { intros H2. left. apply H. }
    assert (Hc2 : (exists y, x = y + 3) -> (x < 3) \/ (x >= 3)).
    { intros H2. left. apply H. }
    apply
      (elim_or
         ((S x) < 3)
         (exists y : nat, (x = (y + 3)))
         _
      ).
    left.
    apply H0. intros. apply Hc2 in H0. destruct H0.
    right.
    
       

  
  induction x.
  - left. auto.
  - right.
    destruct.
    
    exists 0. apply eita. apply H.
    


    exists 0. simpl. 
*)
