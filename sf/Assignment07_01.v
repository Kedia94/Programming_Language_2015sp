Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.
  (* FILL IN HERE *)

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
assert (K: forall a: aexp, aeval (optimize_0plus a) = aeval a).
{ intros a. induction a. reflexivity. destruct a1. simpl in IHa1. simpl. generalize dependent n. induction n. simpl. rewrite IHa2. reflexivity. simpl. rewrite IHa2. reflexivity. auto.
  simpl in IHa1. simpl. rewrite IHa1. rewrite IHa2. reflexivity. simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  repeat (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct a1. destruct n. simpl. reflexivity. simpl. simpl in IHa1. induction n. simpl. rewrite IHa2. reflexivity. rewrite IHa2. reflexivity.
(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
(simpl; rewrite IHa1; rewrite IHa2; reflexivity). }

intros. induction b. reflexivity. reflexivity. simpl.
simpl. rewrite K. rewrite K. reflexivity. simpl. rewrite K. rewrite K. reflexivity. simpl. rewrite IHb. reflexivity. simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  (* FILL IN HERE *)
Qed.
(** [] *)

