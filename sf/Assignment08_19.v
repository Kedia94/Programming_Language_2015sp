Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
unfold constfold_0plus. unfold ctrans_sound. intros. remember (fold_constants_com c) as c'. apply trans_cequiv with c'.
rewrite Heqc'. apply fold_constants_com_sound. apply optimize_0plus_com_sound.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
