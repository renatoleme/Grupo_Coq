  Theorem snd_fst_is_swap: 
    forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros p. 
    destruct p as [n m]. 
    simpl. 
    reflexivity.
  Qed.
  
    Theorem fst_swap_is_snd : forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.
  
  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => 
        if h =? 0 then nonzeros t 
        else h :: nonzeros t
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof.
    simpl. reflexivity.
  Qed.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => 
        if even h 
        then oddmembers t 
        else h :: oddmembers t
    end.

  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof.
    simpl. reflexivity.
  Qed.
  
  Definition countoddmembers 
    (l : natlist) : nat :=
      length (oddmembers l).

  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof.
    reflexivity.
  Qed.

 Example test_countoddmembers2:
   countoddmembers [0;2;4] = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof.
    reflexivity.
  Qed.

  (**)

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
      match l1, l2 with
        nil, nil => nil
      | [], h :: t => h :: t
      | h :: t, [] => h :: t
      | h1 :: t1, h2 :: t2 =>
          let inv_r := h2 in
          let inv_l := h1 in
          inv_l :: inv_r :: (alternate t1 t2) 
      end.

  Compute  alternate [1] [4;5;6].

  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof.
    simpl. reflexivity.
  Qed.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof.
    reflexivity.
  Qed.
  
  
  
    Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t => 
        if h =? v 
        then 1 + (count v t) 
        else (count v t)
    end.

  Example test_count1: 
    count 1 [1;2;3;1;4;1] = 3.
  Proof.
    reflexivity.
  Qed.
  
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof.
    reflexivity.
  Qed.

  Definition sum (b1 b2 : bag) := b1 ++ b2.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Definition add (v : nat) (s : bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition member (v : nat) (s : bag) : bool :=
    if (count v s) =? 0 then false else true.

  Example test_member1: member 1 [1;4;1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof.
    reflexivity.
  Qed.
  
  (* bag_more_functions *)

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
      nil => nil
    | h :: t => if h =? v then t else h :: (remove_one v t)
    end.

  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
      nil => nil
    | h :: t => if h =? v then (remove_all v t) else h :: (remove_all v t)
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.
      
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof.
    reflexivity.
  Qed.
  
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof.
    reflexivity.
  Qed.

  Compute member 1 [1;2;3].

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s1 with
      nil => true
    | h :: t =>
        if andb (member h s2) (count h s1 <=? count h s2)
        then subset t s2 else false
    end.

  Compute subset [1;2;3] [3;2;4;3].
  
  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof.
    reflexivity.
  Qed.

  (*add_inc_count*)
  
  Theorem bag_theorem : forall b : bag, forall v : nat,
      count v (add v b) = S (count v b).
  Proof.
    induction v as [| v' IHv'].
    - simpl. destruct b.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl.
      rewrite eqb_refl. reflexivity.
  Qed.
  


(* Exercícios parte 1 *)
  
  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    induction l as [| n l' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite IHl1'. reflexivity.
  Qed.

  Theorem rev_app_distr: forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2.
    induction l1 as [| n l1' IHl1'].
    - simpl. destruct l2.
      + simpl. reflexivity.
      + simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
  Qed.
     
  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    induction l as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite rev_app_distr. rewrite IHl'.
      simpl. reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite app_assoc. rewrite app_assoc. reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1' IHl1'].
    - simpl. reflexivity.
    - destruct n.
      + simpl. rewrite IHl1'. reflexivity.
      + simpl. rewrite IHl1'. reflexivity.
  Qed.
  
  (**)

  Fixpoint eqblist (l1 l2 : natlist) : bool :=
      match l1, l2 with
        nil, nil => true
      | nil, _ => false 
      | _, nil => false 
      | h1 :: t1, h2 :: t2 => if h1 =? h2 then eqblist t1 t2 else false
      end.

  Example test_eqblist1 :
    (eqblist nil nil = true).
  Proof.
    simpl. reflexivity.
  Qed.

  Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
  Proof.
    simpl. reflexivity.
  Qed.

  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem eqblist_refl : forall l : natlist,
      true = eqblist l l.
  Proof.
    induction l as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite IHl'. rewrite eqb_refl. reflexivity.
  Qed.

  Theorem count_member_nonzero : forall (s : bag),
      1 <=? (count 1 (1 :: s)) = true.
  Proof.
    intros s. simpl. reflexivity.
  Qed.

  Theorem leb_n_Sn : forall n,
      n <=? (S n) = true.
  Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
  Qed.

  (* (remove_does_not_increase_count) *)

  Theorem remove_does_not_increase_count: forall (s : bag),
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    intros s.
    induction s as [| n s' IHs'].
    - simpl. reflexivity.
    - destruct n.
      + simpl. rewrite leb_n_Sn. reflexivity.
      + simpl. rewrite IHs'. reflexivity.
  Qed.

  (**)

  Lemma sum_lemma : forall b : bag,
      sum b [] = b.
  Proof.
    induction b as [| n b' IHb'].
    - simpl. reflexivity.
    - simpl. rewrite IHb'. reflexivity.
  Qed.

  Theorem bag_count_sum : forall (b1 b2 : bag) (n : nat),
      count n (sum b1 b2) = count n b1 + count n b2.
  Proof.
    intros b1 b2 n.
    induction b1 as [| n' b1' IHb1'].
    - (* b1 = nil *)
      reflexivity.
    - (* b1 = cons *)
      simpl.
      rewrite IHb1'.
      destruct (n' =? n).
      + simpl. reflexivity.
      + simpl. reflexivity.
  Qed.

  (**)
  
  Theorem rev_injective : forall (l1 l2 : natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2.
    induction l2 as [| h2 l2'].
    - simpl.
      induction l1 as [| h1 l1'].
      + simpl. reflexivity.
      + simpl. rewrite IHl1'. simpl.
Admitted.

  Theorem eqb_id_refl : forall x : id, eqb_id x x = true.
  Proof.
    intros x.
    destruct x as [n].
    simpl.
    Search (?x =? ?x = true).
    rewrite eqb_refl. reflexivity.
  Qed.
  
  
  
  
      Theorem update_eq : forall 
      (d : partial_map) 
      (x : id) 
      (v : nat),
        find x (update d x v) = Some v.
    Proof.
      intros.
      destruct v.
      - simpl. rewrite eqb_id_refl. reflexivity.
      - simpl. rewrite eqb_id_refl. reflexivity.
    Qed.

    (**)
    
    Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
        eqb_id x y = false -> find x (update d y o) = find x d.
    Proof.
      intros.
      destruct d.
      - simpl. rewrite H. reflexivity.
      - simpl. rewrite H. reflexivity.
    Qed.



    (**)

    (* baz_num_elts
       
       Inductive baz : Type :=
       | Baz1 (x : baz)
       | Baz2 (y : baz) (b : bool).
       
       Quantos baz existem? R: Nenhum. É impossível construiz um baz.
       Embora a definição esteja gramaticalmente correta, não existe nenhum
       objeto que a instancie.
       
       A construçao nunca para. Baz1 Baz1 Baz1 .....
     *)
