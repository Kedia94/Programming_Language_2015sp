Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
intros n m. generalize dependent n. induction m. destruct n. intros. simpl. reflexivity. intro. inversion H.
intro n. destruct n. simpl. reflexivity. simpl. intro. SearchAbout le. apply Sn_le_Sm__n_le_m in H. apply IHm. apply H.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *)
Qed.

