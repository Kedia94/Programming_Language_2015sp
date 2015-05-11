Require Export Assignment07_01.

(* problem #02: 10 points *)

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)

Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
intros. induction a. simpl. reflexivity.
(simpl; rewrite IHa1; rewrite IHa2; reflexivity).
(simpl; rewrite IHa1; rewrite IHa2; reflexivity).
replace (aeval (optimize_1mult (AMult a1 a2))) with (aeval (AMult (optimize_1mult a1) (optimize_1mult a2))).
simpl. rewrite IHa1. rewrite IHa2. reflexivity.
symmetry. destruct a1; destruct a2.
{ destruct n. destruct n0. reflexivity. simpl. destruct n0. reflexivity. simpl. reflexivity. destruct n0. simpl.
  destruct n. reflexivity. reflexivity. simpl. simpl in IHa1. simpl in IHa2. destruct n. simpl. rewrite plus_comm. reflexivity. simpl. destruct n0. simpl. rewrite mult_comm. simpl.  rewrite plus_comm. reflexivity.
  simpl. reflexivity. }
{ destruct n. simpl. reflexivity. simpl. simpl in IHa1. simpl in IHa2. rewrite IHa2. destruct n. simpl. rewrite IHa2. rewrite plus_comm with (m:=0). reflexivity. simpl. rewrite IHa2. reflexivity. }
{ destruct n. simpl. reflexivity. simpl. destruct n. simpl.  rewrite plus_comm with (m:=0). reflexivity. simpl. reflexivity. }
{ destruct n. simpl. reflexivity. destruct n. simpl in IHa1. simpl. rewrite plus_comm with (m:=0). reflexivity. simpl. reflexivity. }
{ destruct n. simpl. reflexivity. simpl. destruct n. simpl. rewrite mult_comm with (m:=1). simpl. rewrite plus_comm with (m:=0). reflexivity. simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. destruct n. simpl. reflexivity. destruct n. simpl. rewrite mult_comm with (m:=1). simpl. rewrite plus_comm with (m:=0). reflexivity. simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. destruct n. reflexivity. simpl. destruct n. simpl. rewrite mult_comm with (m:=1).  simpl.  rewrite plus_comm with (m:=0). reflexivity. simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. reflexivity. }
Qed.

