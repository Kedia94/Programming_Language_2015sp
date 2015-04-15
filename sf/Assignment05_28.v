Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
   p_0 : pal []
  |p_x : forall (x: X), pal [x]
  |p_l : forall (x: X) (l: list X), pal l -> pal (x :: snoc l x).
(* FILL IN HERE *)


Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
intros. induction l. simpl. apply p_0. simpl. rewrite <- snoc_with_append. apply p_l. apply IHl.
  (* FILL IN HERE *)
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
assert (T: forall (X: Type) (x: X) (l: list X), l++[x] = snoc l x).
{ intros. induction l. reflexivity. simpl. rewrite <- IHl. reflexivity. }
intros X l H. induction H. simpl. reflexivity. simpl. reflexivity. simpl. rewrite rev_snoc. rewrite <- T. simpl. rewrite <- T. rewrite <- IHpal. reflexivity.
  (* FILL IN HERE *)
Qed.

(** [] *)




