Require Export Assignment05_23.

(* problem #24: 10 points *)







(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
intros. induction H0. apply H. inversion H. apply IHev. apply pf_evn.
  (* FILL IN HERE *)
Qed.
(** [] *)



