Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
intros. induction n. exists st. split. constructor. apply H.
inversion IHn.
 exists (update x X (S n)). inversion H0.
split. apply par_body_n__Sn in H2. eapply multi_trans. apply H1. apply H2.
unfold update; simpl. split. reflexivity. inversion H2. apply H4.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

