Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
all_nil : all P []
| all_cons : forall x xs, P x -> all P xs -> all P (x :: xs)
  (* FILL IN HERE *)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
intros. split.
{ induction l. intro. apply all_nil. simpl. intro. apply all_cons.
  destruct (P x). reflexivity. unfold andb in H. inversion H. apply IHl.
  destruct (forallb P l). reflexivity. unfold andb in H. destruct (P x). inversion H. inversion H. }
{ induction l. simpl. reflexivity. simpl. intro. remember (P x) as px. destruct px. simpl.
  apply IHl. inversion H. apply H3. inversion H. rewrite <- Heqpx in H2. inversion H2. }
  (* FILL IN HERE *)
Qed.

(** [] *)

