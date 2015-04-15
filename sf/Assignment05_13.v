Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
intros. unfold not. generalize dependent m.
induction n. induction m. simpl. intros. inversion H.
simpl. intros. inversion H0.
intros. induction m. inversion H0.
apply (IHn m). simpl in H. apply H. inversion H0. reflexivity. 
  (* FILL IN HERE *)
Qed.
(** [] *)



