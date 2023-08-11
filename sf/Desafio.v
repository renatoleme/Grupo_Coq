Require Import List.
Import ListNotations.

Check [1;2;3;4].

Definition hd
  (default : nat) 
  (l : list nat) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl 
  (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* 
A função nonzeros recebe uma lista de naturais e remove cada ocorrência do número zero nessa lista. *)
Fixpoint nonzeros 
  (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => 
      match h with
      | 0 => (nonzeros t)
      | S n => h :: (nonzeros t)
      end
end.

Compute nonzeros [].
Compute nonzeros [0;6;4;0;2].
Compute nonzeros [0;1;0].
Compute nonzeros [1;2;3].
Compute nonzeros [0;0;0].
Compute nonzeros [3;0;2;0;1].

(* 

  Como provar que nonzeros sempre funciona?
  
  ==> Podemos confiar na implementação?
  
  Precisamos: descrever o que significa o programa ser correto e completo e, então, demonstrar com relação a nonzeros.

*)

Fixpoint LivreDeZero (l : list nat) : bool :=
  match l with
  | nil => true
  | h :: tl => 
      if (Nat.eqb h 0) then false
        else LivreDeZero tl
end.
 
Theorem nonzeros_correct : forall (l : list nat),
  LivreDeZero (nonzeros l) = true.
Proof.
  intros l.
  induction l as [| h tl IHl ].
  - simpl. reflexivity.
  - destruct h.
    + simpl. apply IHl.
    + simpl. apply IHl.
Qed.



