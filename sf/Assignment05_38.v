Require Export Assignment05_37.

(* problem #38: 10 points *)

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
intros n m o bnm bmo. apply ble_nat_true in bnm. apply ble_nat_true in bmo. SearchAbout le. apply le_ble_nat. SearchAbout le. apply (le_trans n m o).
apply bnm. apply bmo.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *)
Qed.

