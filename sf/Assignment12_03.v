Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
intros. generalize dependent T'.
induction TYPED; subst.
intros. inversion TYPED'. rewrite H in H2. inversion H2; reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED in H4. rewrite H4. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED1 in H2. apply IHTYPED2 in H4. subst. inversion H2. reflexivity.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED2 in H5. assumption.
intros. inversion TYPED'; subst. apply IHTYPED1 in H2. apply IHTYPED2 in H4. subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED in H1. inversion H1. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED in H1. inversion H1. reflexivity.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED1 in H4. subst. apply IHTYPED2 in H5. assumption.
intros. inversion TYPED'; subst. apply IHTYPED in H3. subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED in H3. subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED1 in H6. inversion H6. subst. apply IHTYPED2 in H7. assumption.
intros. inversion TYPED'; subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED1 in H2. subst. reflexivity.
intros. inversion TYPED'; subst. apply IHTYPED1 in H6. inversion H6. subst. apply IHTYPED2 in H7. assumption.
intros. inversion TYPED'; subst. apply IHTYPED in H1. inversion H1. reflexivity.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

