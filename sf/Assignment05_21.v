Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
intros. induction H. apply H0. induction H0. simpl. apply ev_SS. apply IHev.
simpl. apply ev_SS. apply IHev. 
  (* FILL IN HERE *)
Qed.
(** [] *)





