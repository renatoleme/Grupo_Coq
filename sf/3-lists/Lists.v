From LF Require Export Induction.

Module NatList.

  Inductive natprod : Type := 
  | pair (n1 n2 : nat).

  Check pair 3 2.
  Check pair 4 5.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Compute snd (pair 2 5).

  Notation "( x , y )" := 
  (pair x y).
  
  Check (2, 4).
  Check (5, 7).
  
  Compute (fst (3, 5)).
  
  (* Novas definições, agora usando a notation. *)

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x, y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x, y) => y
    end.

  Definition swap_pair 
  (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.
  
  (* O mesmo teorema, escrito de formas diferentes. No primeiro, não precisamos usar destruct. *)
  
  Theorem surjective_pairing' : 
    forall (n m : nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    intros n m. simpl.
    reflexivity.
  Qed.

  Theorem surjective_pairing : 
    forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p. 
    simpl. (* Não faz nada *) 
    destruct p as [n' m'].
    simpl. reflexivity.
  Qed.

  (* Exercício *)

  Theorem snd_fst_is_swap: 
    forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof. 
    intros p.
    destruct p as [n m].
    simpl. reflexivity. 
  Qed.

  Theorem fst_swap_is_snd : 
    forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intros p.
    destruct p as [n m].
    simpl. reflexivity.
  Qed.

  (* *******
    List of numbers
    
    * Iremos generalizar a noção de par.
    
  ******* *)
  
  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  
  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l)
                       (at level 60, 
                        right associativity).
  Notation "[]" := nil.
  Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).
    
   Check [1;2;3;4;5;6].

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => 
      n :: (repeat n count')
    end.
    
  Compute repeat 3 5.

  Fixpoint length 
    (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.
    
  Compute length [1;2;3;2;5;7;3].
  Compute length (repeat 2 4).

  Fixpoint app 
  (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := 
    (app x y) 
    (right associativity, 
    at level 60).

  Example test_appl: 
  [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof.
    simpl. reflexivity.
  Qed.

  Example test_app2: nil ++ [4;5] = [4;5].
  Proof.
    reflexivity.
  Qed.

  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof.
    reflexivity.
  Qed.

  Definition hd
    (default : nat)
    (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tl 
  (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Example test_hd1 : 
  hd 0 [1;2;3] = 1.
  Proof. reflexivity. Qed.
  Example test_hd2 : hd 0 [] = 0.
  Proof. reflexivity. Qed.
  Example test_tl: 
  tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.

  (* Exercícios *)

  (*Fixpoint nonzeros (l : natlist) : natlist.
  Admitted.*)

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. Admitted.

  Fixpoint oddmembers (l : natlist) : natlist.
  Admitted.

  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. Admitted.
  
  Definition countoddmembers 
    (l : natlist) : nat. Admitted.

  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. Admitted.

 Example test_countoddmembers2:
   countoddmembers [0;2;4] = 0.
  Proof. Admitted.

  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. Admitted.

  (**)

  Fixpoint alternate 
    (l1 l2 : natlist) : natlist. Admitted.

  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. Admitted.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. Admitted.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. Admitted.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. Admitted.

  (* Bag *)

  Definition bag := natlist.

  Fixpoint count 
  (v : nat) (s : bag) : nat. Admitted.
  
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. Admitted.

  Definition sum (b1 b2 : bag) := b1 ++ b2.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. Admitted.

  Definition add (v : nat) (s : bag) : bag. Admitted.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. Admitted.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. Admitted.

  Definition member (v : nat) (s : bag) : bool :=
    if (count v s) =? 0 then false else true.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. Admitted.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. Admitted.
  
  (* bag_more_functions *)

  Fixpoint remove_one (v : nat) (s : bag) : bag. Admitted.

  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. Admitted.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. Admitted.
  
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. Admitted.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. Admitted.

  Fixpoint remove_all (v : nat) (s : bag) : bag. Admitted.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. Admitted.
      
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. Admitted.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. Admitted.
  
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. Admitted.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool. Admitted.
  
  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. Admitted.

  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. Admitted.

  (*add_inc_count*)
  
  Theorem bag_theorem : forall b : bag, forall v : nat,
      count v (add v b) = S (count v b).
  Proof. Admitted.

  (* 
     Reasoning about lists
   *)

  Theorem nil_app : forall l : natlist,
      [] ++ l = l.
  Proof.
    intros l.
    simpl.
    reflexivity.
  Qed.
  
  Theorem tl_length_pred : 
  forall l : natlist,
      pred 
      (length l) = length (tl l).
  Proof.
    intros l. destruct l as [| n l'].
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.
      
  (* 
     Induction on Lists
   *)

  Theorem app_assoc : 
  forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = 
      l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. 
    induction l1 as [ | n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite IHl1'. reflexivity.
  Qed.

  (* Reversing a list *)

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof.
    reflexivity.
  Qed.

  Example test_rev2 : rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem app_length : forall l1 l2 : natlist, 
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite IHl'. reflexivity.
  Qed.
 
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
      simpl. reflexivity.
    - (* l = n :: l' *)
      simpl. rewrite app_length.
      rewrite IHl'. rewrite add_comm. simpl. reflexivity.
  Qed.

  (* Search *)
  
  Search rev.
  Search (_ + _ = _ + _).
  Search (_ + _ = _ + _) inside Induction.
  Search (?x + ?y = ?y + ?x).

  (* Exercícios parte 1 *)
  
  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof. Admitted.

  Theorem rev_app_distr: forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof. Admitted.
     
  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof. Admitted.
  
  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = 
      ((l1 ++ l2) ++ l3) ++ l4.
  Proof. Admitted.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = 
      (nonzeros l1) ++ (nonzeros l2).
  Proof. Admitted.
  
  (**)

  Fixpoint eqblist (l1 l2 : natlist) : bool. Admitted.

  Example test_eqblist1 :
    (eqblist nil nil = true).
  Proof. Admitted.
  Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
  Proof. Admitted.

  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof. Admitted.

  Theorem eqblist_refl : forall l : natlist,
      true = eqblist l l.
  Proof. Admitted.

  Theorem count_member_nonzero : forall (s : bag),
      1 <=? (count 1 (1 :: s)) = true.
  Proof. Admitted.

  Theorem leb_n_Sn : forall n,
      n <=? (S n) = true.
  Proof. Admitted.

  (* (remove_does_not_increase_count) *)

  Theorem remove_does_not_increase_count: forall (s : bag),
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof. Admitted.

  (**)

  Lemma sum_lemma : forall b : bag,
      sum b [] = b.
  Proof. Admitted.

  Theorem bag_count_sum : forall (b1 b2 : bag) (n : nat),
      count n (sum b1 b2) = count n b1 + count n b2.
  Proof. Admitted.

  (**)
  
  Theorem rev_injective : forall (l1 l2 : natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof. Admitted.

  (* Options (Em Haskell: Maybe ... ) *)

  Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

  Compute nth_bad [1;5;8] 5.

  Inductive natoption : Type :=
  | Some (n : nat)
  | None.

  Fixpoint nth_error 
  (l : natlist) (n : nat) : natoption :=
    match l with
    | nil => None
    | a :: l' =>
        match n with
        | O => Some a
        | S n' => nth_error l' n'
        end
    end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  (* Exercicios *)
  (* Vamos fazer estes. *)
  
  Definition hd_error 
    (l : natlist) : natoption. Admitted.

  Example test_hd_error1 : hd_error [] = None.
  Proof. Admitted.
  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. Admitted.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. Admitted.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
      hd default l = option_elim default (hd_error l).
  Proof. Admitted.

  (* Partial maps *)

  Inductive id : Type := Id (nat : nat).
  
  Check Id 34.

  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
      Id n1, Id n2 => n1 =? n2
    end.

  (* Exercícios *)

  Theorem eqb_id_refl : forall x : id, eqb_id x x = true.
  Proof. Admitted.
  
  Module PartialMap.

    Inductive partial_map : Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).

    Definition update 
      (d : partial_map) 
      (x : id) 
      (value : nat) : partial_map :=
        record x value d.

    Fixpoint find (x : id) (d : partial_map) : natoption :=
      match d with
      | empty => None
      | record y v d' => if eqb_id x y
                         then Some v
                         else find x d'
      end.

    (* Exercícios *)

    Theorem update_eq : forall 
      (d : partial_map) 
      (x : id) 
      (v : nat),
        find x (update d x v) = Some v.
    Proof. Admitted.

    (**)

    Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
        eqb_id x y = false -> find x (update d y o) = find x d.
    Proof. Admitted.

  End PartialMap.

 
 Fixpoint  nonzeros (l : natlist) : natlist :=
 match l with
 | nil => nil
 | h :: t => match h with
              | 0 => (nonzeros t)
              | S n => h :: (nonzeros t)
             end
 end.
 
Compute nonzeros [0;6;4;0;2].

Fixpoint LivreDeZero (l : natlist) : bool :=
match l with
| nil => true
| h :: tl => if (Nat.eqb h 0) then false
 else LivreDeZero tl
end.

Theorem nonzeros_correct : forall (l : natlist),
  LivreDeZero (nonzeros l) = true.
Proof. 
  intros l.
  induction l as [| h tl IHl ].
  - simpl. reflexivity.
  - destruct h. 
    +  simpl. apply IHl.
    +  simpl. apply IHl.
Qed.

End NatList.



