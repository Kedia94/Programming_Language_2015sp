Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
unfold atrans_sound. intros. unfold aequiv. intros.
aexp_cases (induction a) Case; simpl.
reflexivity.
reflexivity.
{ rewrite IHa1. rewrite IHa2. generalize dependent a2. destruct a1. destruct n. intros. simpl. reflexivity.
  { destruct a2. simpl. destruct n0. simpl. intro.  rewrite plus_comm. reflexivity. simpl. reflexivity.
    simpl. reflexivity. reflexivity. reflexivity. reflexivity. }
  { destruct a2. simpl. destruct n. simpl. rewrite plus_comm. reflexivity. simpl. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. }
  { destruct a2. intros. destruct n. simpl in IHa2. rewrite plus_comm. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. }
  { destruct a2. destruct n. simpl. rewrite plus_comm. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. }
  { destruct a2. destruct n. simpl. rewrite plus_comm. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. }
}
rewrite IHa1. rewrite IHa2. reflexivity.
rewrite IHa1. rewrite IHa2. reflexivity.
Qed.
(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

