(* DO NOT Require Import other files. *)

Require Import Basics.


Module NatlistProblems.

(*** 
   See the chapter "Lists" for explanations of the following.
 ***)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.  
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.









(** **** Problem #1 (10 pts) : 2 stars (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | a :: b => a :: nonzeros b
end.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
unfold nonzeros.
reflexivity.
Qed.
 (* FILL IN HERE *)

(** [] *)








(** **** Problem #2 (10 pts): 3 stars, advanced (alternate) *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
   match l1, l2 with
   | nil, _ => l2
   | _, nil => l1
   | a::b, c::d => a::(c::alternate b d)
end.
 (* FILL IN HERE *)

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
unfold alternate. reflexivity.
Qed.
 (* FILL IN HERE *)
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
unfold alternate. reflexivity.
Qed.
 (* FILL IN HERE *)
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
unfold alternate. reflexivity.
Qed.
 (* FILL IN HERE *)
Example test_alternate4:        alternate [] [20;30] = [20;30].
unfold alternate. reflexivity.
Qed.
 (* FILL IN HERE *)
(** [] *)








(** **** Problem #3 (60 pts) : 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
intros. elim l. reflexivity.
intros. simpl. rewrite H. reflexivity. 
Qed.
  (* FILL IN HERE *)


(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
assert (snoc_assert: forall l:natlist, forall v:nat, snoc l v = l++[v]).
{ intros. elim l. reflexivity. intros. unfold snoc. fold snoc. rewrite H. reflexivity. }
assert (rev_assert: forall a b:natlist, rev (a++b) = rev b ++ rev a).
{ intros. elim a. simpl. rewrite app_nil_end. reflexivity.
  intros. simpl. rewrite H. rewrite snoc_assert. rewrite snoc_assert. rewrite app_assoc. reflexivity. }
intros. elim l. reflexivity.
intros. unfold rev. fold rev. rewrite (snoc_assert (rev n0) n). unfold rev.  fold rev. simpl. rewrite rev_assert. rewrite H. reflexivity.
Qed.   
  (* FILL IN HERE *)


(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros.
rewrite (app_assoc (l1++l2) l3 l4).
rewrite (app_assoc l1 l2  (l3++l4)).
reflexivity.
Qed.
  (* FILL IN HERE *)


Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
intros. elim l. simpl. reflexivity.
intros. unfold snoc. fold snoc. simpl. rewrite H. reflexivity.
Qed.
  (* FILL IN HERE *)


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
assert (snoc_assert: forall l:natlist, forall v:nat, snoc l v = l++[v]).
{ intros. elim l. reflexivity. intros. unfold snoc. fold snoc. rewrite H. reflexivity. }
intros. elim l1. simpl. rewrite app_nil_end. reflexivity.
  intros. simpl. rewrite H. rewrite snoc_assert. rewrite snoc_assert. rewrite app_assoc. reflexivity.
Qed.
  (* FILL IN HERE *)


(** An exercise about your implementation of [nonzeros]: *)
Theorem nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros. elim l1. simpl. reflexivity.
intros. elim n. simpl. rewrite H. reflexivity.
intros. unfold nonzeros. simpl. fold nonzeros. rewrite H. reflexivity.
Qed. 
  (* FILL IN HERE *)

(** [] *)










(** **** Problem #4 (20 pts) : 2 stars (beq_natlist) *)
(*Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.*)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. 

    You can use [beq_nat] from Basics.v
*)

Check beq_nat.
Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | a::b, c::d => (andb (beq_nat a c) (beq_natlist b d))
  | [], [] => true
  | a::b, [] => false
  | [], c::d => false
end.
  (* FILL IN HERE *)

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 simpl. reflexivity. Qed.
 (* FILL IN HERE *)
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
simpl. reflexivity. Qed.
 (* FILL IN HERE *)
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
simpl. reflexivity. Qed.
 (* FILL IN HERE *)

(** Hint: You may need to first prove a lemma about reflexivity of beq_nat. *)
Theorem beq_natlist_refl : forall l:natlist,
  beq_natlist l l = true.
Proof.
assert (H: forall n: nat, beq_nat n n = true).
{ intros. elim n. simpl. reflexivity. intros. simpl. rewrite H. reflexivity. }
 intros. elim l. simpl. reflexivity.
 intros. unfold beq_natlist. fold beq_natlist. rewrite H. rewrite H0. reflexivity.
Qed.
  (* FILL IN HERE *)
(** [] *)

















(** **** Problem #5 (10 pts) : 4 stars, advanced (rev_injective) *)

(** Hint: You can use the lemma [rev_involutive]. *)
Theorem rev_injective: forall l1 l2 : natlist, 
  rev l1 = rev l2 -> l1 = l2.
Proof.
intros. 
rewrite <-(rev_involutive l1). rewrite H. rewrite rev_involutive. reflexivity.
Qed.
  (* FILL IN HERE *)

(** [] *)
















(** **** Problem #6 (20 pts) : 2 stars (hd_opt) *)
(** Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
   match l with
   | [] => None
   | a::b => Some a
end.
  (* FILL IN HERE *)

Example test_hd_opt1 : hd_opt [] = None.
simpl. reflexivity.
Qed.
 (* FILL IN HERE *)

Example test_hd_opt2 : hd_opt [1] = Some 1.
simpl. reflexivity.
Qed.
 (* FILL IN HERE *)

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
simpl. reflexivity.
Qed.
 (* FILL IN HERE *)
(** [] *)


(** This exercise relates your new [hd_opt] to the old [hd]. *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
intros. elim l. simpl. reflexivity.
intros. simpl. reflexivity.
Qed.
  (* FILL IN HERE *)
(** [] *)




End NatlistProblems.
















Module Poly.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil   => 0
  | cons h t => S (length X t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.  (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.










(** **** Problem #7 (20 pts) : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
   match l with
   | [] => ([],[])
   | a::b => (((fst a) :: (fst (split b))), ((snd a) :: (snd (split b))))
end.
(* FILL IN HERE *)

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
simpl. reflexivity.
Qed.
(* FILL IN HERE *)

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
intros. elim l. simpl. reflexivity.
intros. simpl. rewrite H. reflexivity.
Qed.
(* FILL IN HERE *)

(** [] *)



End Poly.
