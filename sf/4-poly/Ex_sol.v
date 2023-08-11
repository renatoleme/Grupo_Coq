Theorem app_nil_r :
  forall (X : Type), forall l : list X,
    l ++ [] = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc :
  forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length :
  forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

(**)

Theorem rev_app_distr :
  forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - simpl. induction l2.
    + simpl. reflexivity.
    + simpl. rewrite IHl2. rewrite app_nil_r. simpl.
      rewrite app_nil_r. reflexivity.
  - simpl.
    rewrite IHl1. simpl. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive: 
  forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof.
  induction l as [| n l' IHl].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.