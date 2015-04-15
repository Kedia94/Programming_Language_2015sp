Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
intros. generalize dependent n. induction m. destruct n. intro. apply O_le_n. simpl. intro. inversion H.
simpl. intros. destruct n. apply O_le_n. simpl in H. SearchAbout le. apply n_le_m__Sn_le_Sm. apply IHm. apply H. 
  (* FILL IN HERE *)
Qed.

