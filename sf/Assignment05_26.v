Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
intros. induction n. simpl. split. intro. apply ev_0. intro. apply ev_0.
simpl. induction IHn. split. apply H0. destruct n. intro. inversion H1. simpl in H. intro. apply ev_SS. apply H. inversion H1. apply H3. 
  (* FILL IN HERE *)
Qed.
(** [] *)


