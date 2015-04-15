Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt.
intros n1 n2 m. intro. split. SearchAbout le. apply (le_trans (S n1) (S (n1+n2)) m). apply n_le_m__Sn_le_Sm. apply le_plus_l. apply H.
apply (le_trans (S n2) (S (n1+n2)) m). apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l. apply H.
  
 (* FILL IN HERE *)
Qed.

