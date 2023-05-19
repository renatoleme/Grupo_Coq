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