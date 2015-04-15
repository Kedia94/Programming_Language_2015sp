Require Export Assignment05_26.

(* problem #27: 10 points *)
Definition nat_ind2: forall (P: nat -> Prop), 
           P 0 -> 
           P 1 -> 
          (forall n: nat, P n -> P (S(S n))) -> 
          forall n: nat, P n := 
                     fun P => fun P0 => fun P1 => fun PSS => 
                     fix f (n: nat) := match n return P n with 0 => P0 | 1 => P1 | S (S n') => PSS n' (f n')
end.


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
intro n. unfold even. intro H.
induction n using nat_ind2. apply ev_0. inversion H. apply ev_SS. apply IHn. simpl in H. apply H.
  (* FILL IN HERE *)
Qed.
(** [] *)



