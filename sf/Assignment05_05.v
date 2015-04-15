Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R. split.
 - intros. inversion H as [HP | [HQ HR]]. split. left. apply HP. left. apply HP. split. right. apply HQ. right. apply HR.
 - intros. inversion H. inversion H0. left. apply H2. inversion H1. left. apply H3. right. split. apply H2. apply H3.
  (* FILL IN HERE *)
Qed.
(** [] *)


