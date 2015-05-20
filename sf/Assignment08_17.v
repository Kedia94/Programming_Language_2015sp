Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
unfold btrans_sound. intros. unfold bequiv. intros.
bexp_cases (induction b) Case. reflexivity. reflexivity.
 assert (aeval st a = aeval st (optimize_0plus_aexp a)) as Ha1. apply optimize_0plus_aexp_sound. assert (aeval st a0 = aeval st (optimize_0plus_aexp a0)) as Ha2.
 apply optimize_0plus_aexp_sound. simpl. rewrite -> Ha1. rewrite -> Ha2. reflexivity.
simpl. assert (aeval st a = aeval st (optimize_0plus_aexp a)) as Ha1. apply optimize_0plus_aexp_sound. assert (aeval st a0 = aeval st (optimize_0plus_aexp a0)) as Ha2.
apply optimize_0plus_aexp_sound. rewrite -> Ha1. rewrite -> Ha2. reflexivity.
simpl. rewrite <- IHb. reflexivity. simpl. rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

