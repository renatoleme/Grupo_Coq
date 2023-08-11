From LF Require Export Lists.


(* Polimorfismo e funções de alta ordem. *)

(* PARTE 1: POLIMORFISMO *)

(* Motivação *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(*

  Um tipo de lista para cada tipo de dado
  ---> Todas as funções precisariam ser redefinidas!

 *)

(* Polimorfismo *)

Inductive list (X : Type) : Type :=
| nil
| cons : X -> list X -> list X.

(* 

 '' What sort of thing is list itself? 
  (...) list is a function from Types to Type ''

*)

Check list : Type -> Type.

Check list nat.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check nil bool.

Check nil nat.

Check cons.

Fixpoint repeat
  (X : Type)
  (x : X)
  (count : nat) : list X :=
  match count with
    0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Compute repeat nat 5 4.
Compute repeat bool true 4.

(* Exercício mumble_grumble *)

Module MumbleGrumble.

  Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

  Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

  (*
      Qual dos Checks abaixo vai retornar 
      grumble X, para algum tipo X? 
  *)

  (* Check d (b a 5). *)
  (* Check d mumble (b a 5). *)
  (* Check d bool (b a 5). *)
  (* Check e bool true. *)
  (* Check e mumble (b c 0). *)
  (* Check e bool (b c 0). *)
  (* Check c. *)

End MumbleGrumble.

Fixpoint repeat' X x count :=
  match count with
    0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Fixpoint repeat'' X x count : list X :=
  match count with
    O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123' := 
cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Forçando type inference: *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Compute repeat true 8.

Definition list123'' := 
cons 1 (cons 2 (cons 3 nil)).

(* 
    Um outro jeito de forçar o type inference é 
    na  declaração do tipo: 
*)

Fixpoint repeat'''
  {X : Type}
  (x : X)
  (count : nat) : list X :=
  match count with
    O => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X : Type} : Type :=
| nil'
| cons' (x : X) (l : list').

(* 
  Problema: ambas as listas são list'
    (e não list nat e list bool)
*)
Check cons' true (cons' false (nil')) : list'.
Check cons' 3 (cons' 2 (nil')) : list'.

(* Isso não ocorre no caso de uso do Arguments *)

Check cons true (cons false (nil)) : list bool.
Check cons 3 (cons 2 (nil)) : list nat.

(************)
(* Re-definindo outras funções, agora usando polimorfismo e type inference. *)
(************)

Fixpoint app
  {X : Type}
  (l1 l2 : list X) : list X :=
  match l1 with
    nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev
  {X : Type}
  (l : list X) :=
  match l with
    nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length 
  {X : Type} 
  (l : list X) : nat :=
  match l with
    nil => O 
  | cons _ t => S (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) 
  = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) 
  = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: 
  length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* As vezes, o type inference falha. *)

Fail Definition mynil := nil.

(* Neses casos, devemos ser explícitos: *)

Definition mynil : list nat := nil.

(* Alternativamente, podemos forçar os argumentos implícitos a serem explícitos prefixando o nome da função com @ *)

Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" 
  := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" 
  := (cons x .. (cons y []) ..).
Notation "x ++ y" 
  := (app x y) (at level 60, right associativity).

(* Exercícios *)

Theorem app_nil_r :
  forall (X : Type), forall l : list X,
    l ++ [] = l. 
Admitted.

Theorem app_assoc :
  forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n. 
Admitted.

Lemma app_length :
  forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Admitted.

(**)

Theorem rev_app_distr :
  forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Admitted.

Theorem rev_involutive: 
  forall X : Type, forall l : list X,
    rev (rev l) = l.
Admitted.

(* Pares polimórficos *)

Inductive prod (X Y : Type) : Type :=
  pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
    (x, y) => y
  end.

Check (true, 2).

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
    match lx, ly with
      [], _ => []
    | _, [] => []
    | x :: tx, y :: ty => (x, y) :: (combine tx ty)
    end.

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

(**)

Fixpoint split {X Y : Type} (l : list (X * Y)) : list X * list Y :=
  match l with
    nil => ([], [])
  | h :: t => ([fst h] ++ (fst (split t)),
                [snd h] ++ (snd (split t)))
  end. 

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl. reflexivity.
Qed.

(**)

Module OptionPlayground.

  Inductive option (X : Type) : Type :=
    Some (x : X)
  | None.

  Arguments Some {X}.
  Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
    nil => None
  | a :: l' =>
      match n with
        O => Some a
      | S n' => nth_error l' n'
      end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* Exercício *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    nil => None
  | h :: t => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(*
  Functions as data
*)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* Filter *)

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
    [] => []
  | h :: t =>
      if test h then h :: (filter test t)
      else filter test t
  end.

Example test_filter1 : filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2 :
  filter length_is_1
         [[1;2]; [3]; [4]; [5;6;7]; []; [8]] = [[3]; [4]; [8]].
Proof.
  simpl. reflexivity.
Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Anonymous functions : parece JS :) *)

Example test_anon_fun' :
  doit3times (fun n => n * n) 2 = 256.
Proof.
  reflexivity.
Qed.

Example test_filter2' :
  filter (fun l => (length l) =? 1)
         [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof.
  reflexivity.
Qed.

(* Exerícios *)

(* filter_even_gt7 *)

Definition filter_even_gt7 (l : list nat) :=
  filter (fun n => andb (even n) (7 <=? n)) l.
           
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* partition *)

Definition partition {X : Type}
           (test : X -> bool) (l : list X) : list X * list X :=
  ((filter (test) l), (filter (fun el => negb (test el)) l)).
  
Compute  partition odd [1;2;3;4;5].

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Map *)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
    [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2 : map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3 : map (fun n => [even n; odd n]) [2;1;2;5]
                    = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercícios *)

Lemma map_app_distr : forall (X Y : Type) (f : X -> Y) (l1: list X) (el : X),
    map f (l1 ++ [el]) = map f l1 ++ [f el].
Proof.
  intros.
  induction l1 as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.
  
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  induction l as [| h t' IHl].
  - simpl. reflexivity.
  - simpl. rewrite map_app_distr. rewrite IHl. reflexivity.
Qed.
    
(* flat_map *)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
    nil => nil
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(**)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    None => None
  | Some x => Some (f x)
  end.

(* Fold *)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Compute fold mult [3;2;3] 1.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition is_is (n : nat) : bool := n <=? 3.

(* EX: fold_length é um exemplo. Recebe lista de qualquer 
   tipo e sempre retorna nat. *)

(* 
   Functions that construct functions 
 *)

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Compute ftrue 76894.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 299 = 5.
Proof. reflexivity. Qed.

(* partial application example *)

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(**)

Module Exercises.

  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ n => S n) l 0.

  Compute fold_length [true; false; true].

  Example test_fold_length1 : fold_length [4;7;0] = 3.
  Proof. reflexivity. Qed.

  Lemma fold_length_lemma : forall X (h : X) (t : list X),
      fold_length (h :: t) = fold_length ([h]) + fold_length t.
  Proof.
    intros.
    destruct t.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.
      
  Theorem fold_length_correct : forall X (l : list X),
      fold_length l = length l.
  Proof.
    induction l as [| h t IHt].
    - simpl. reflexivity.
    - simpl. rewrite <- IHt. reflexivity.
  Qed.

  (* fold_map *)
  
  Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    fold (fun n => app [(f n)]) l [].

  Definition fold_map_correct : forall (X Y : Type) (l : list X) (f : X -> Y),
      fold_map f l = map f l.
  Proof.
    intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite <- IHl. reflexivity.
  Qed.

  (* currying *)

  Definition prod_curry {X Y Z : Type}
             (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

  Definition prod_uncurry {X Y Z : Type}
             (f : X -> Y -> Z) (p : X * Y) : Z :=
    f (fst p) (snd p).

  Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
  Proof. reflexivity. Qed.

  Check @prod_curry.
  Check @prod_uncurry.

  Theorem uncurry_curry : forall (X Y Z : Type)
                                 (f : X -> Y -> Z)
                                 x y,
      prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    reflexivity.
  Qed.

  Theorem curry_uncurry : forall (X Y Z : Type)
                                 (f : (X * Y) -> Z) (p : X * Y),
      prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    destruct p.
    - simpl. reflexivity.
  Qed.

  Theorem length_nth_error : forall X l n, length l = n -> @nth_error X l n = None.
  Proof.
    intros. induction l.
    - simpl. reflexivity.
    - rewrite <- H. simpl. rewrite <- IHl. 
  Admitted.
    
  (* Church numerals *)

  Module Church.
    
    Definition cnat := forall X : Type, (X -> X) -> X -> X.

    Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.
    Definition one  : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
    Definition two  : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).
    Definition three : cnat := @doit3times.

    Check @doit3times.
    
    Definition succ (n : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f (n X f x).
    
    Example succ_1 : succ zero = one.
    Proof. reflexivity. Qed.
    Example succ_2 : succ one = two.
    Proof. reflexivity. Qed.
    Example succ_3 : succ two = three.
    Proof. reflexivity. Qed.
    
    (**)
    
    Definition plus (n m : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => (m X f) (n X f x).

    Compute plus zero one.
    
    Example plus_1 : plus zero one = one.
    Proof. reflexivity. Qed.
    Example plus_2 : plus two three = plus three two.
    Proof. reflexivity. Qed.
    Example plus_3 : plus (plus two two) three = plus one (plus three three).
    Proof. reflexivity. Qed.

    (**)
    
    Definition mult (n m : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => (n X (m X f) x).
    
    Example mult_1 : mult one one = one.
    Proof. reflexivity. Qed.      
    Example mult_2 : mult zero (plus three three) = zero.
    Proof. reflexivity. Qed.
    Example mult_3 : mult two three = plus three three.
    Proof. reflexivity. Qed.

    (**)
    
    Definition exp (n m : cnat) : cnat :=
      fun X => (m (X -> X)) (n X).
    
    Compute exp three two.

    Example exp_1 : exp two two = plus two two.
    Proof. reflexivity. Qed.
    Example exp_2 : exp three zero = one.
    Proof. reflexivity. Qed.
    Example exp_3 : exp three two = plus (mult two (mult two two)) one.
    Proof. reflexivity. Qed.

  End Church.
End Exercises.
    
    
