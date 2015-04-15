Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
intros n m p Enm Enp. apply ev_sum with (n:=n+m) (m:=n+p) in Enm. replace ((n+m) + (n+p)) with ((n+n) + (m+p)) in Enm. replace (n+n) with (double n) in Enm.
apply (ev_ev__ev (double n) (m+p)) in Enm. apply Enm. apply double_even. apply double_plus.
- rewrite <- plus_assoc. rewrite <- plus_assoc. rewrite (plus_assoc n m p). rewrite (plus_comm n m). rewrite (plus_assoc m n p). reflexivity.
- apply Enp.
  (* FILL IN HERE *)
Qed.
(** [] *)


