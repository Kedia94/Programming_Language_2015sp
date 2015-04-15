Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
intros.
assert (T: forall n, n = n+0).
{ intros. induction n. reflexivity. simpl. rewrite <- IHn. reflexivity. }
induction b. rewrite <- T. apply le_n. replace (a + S b) with (S(a+b)). apply le_S. apply IHb.
induction a. simpl. reflexivity. simpl. rewrite (plus_comm a (S b)). simpl. rewrite plus_comm. reflexivity. 
  (* FILL IN HERE *)
Qed.

