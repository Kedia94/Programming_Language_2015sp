Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
intros. generalize dependent st. induction c.
intros. exists st. constructor.
intros st. exists (update st i (aeval st a)). constructor. reflexivity.
intros. inversion NOWHL. assert (H1:= H0). apply andb_true_elim1 in H0. apply IHc1 with st in H0. inversion H0. apply andb_true_elim2 in H1. apply IHc2 with x in H1. inversion H1. exists x0. apply E_Seq with x. apply H. apply H2.
intros. inversion NOWHL. assert (H1:=H0). apply andb_true_elim1 in H0. apply andb_true_elim2 in H1. apply IHc1 with st in H0. apply IHc2 with st in H1. inversion H0. inversion H1.
remember (beval st b) as eval_b. destruct eval_b.
exists x. apply E_IfTrue. rewrite Heqeval_b. reflexivity. apply H. exists x0. apply E_IfFalse. rewrite Heqeval_b. reflexivity. apply H2.
intros. inversion NOWHL.
Qed.
(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

