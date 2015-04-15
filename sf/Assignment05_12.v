Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
intros. unfold not in H. generalize dependent m. induction n.
induction m. simpl. intros. 
assert (T: forall (P: Prop), False -> P).
{ intros. inversion H0. }
apply T. apply H. reflexivity.
intros. simpl. reflexivity.
induction m. intros. simpl. reflexivity.
simpl. intros. apply IHn. intros. apply H. apply f_equal. apply H0.
Qed.
(** [] *)




