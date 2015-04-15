Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros. split. inversion H. inversion H0.
intros. apply H3. apply H1. apply H5.
intros. inversion H. inversion H0. apply H3. apply H5. apply H1.
  (* FILL IN HERE *)
Qed.


