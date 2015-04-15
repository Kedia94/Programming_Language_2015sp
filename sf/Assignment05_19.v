Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
intros. induction H. apply H0. apply g_plus3. apply IHgorgeous. apply g_plus5. apply IHgorgeous. 
 (* FILL IN HERE *)
Qed.
(** [] *)



