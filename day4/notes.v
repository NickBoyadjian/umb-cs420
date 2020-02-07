Lemma zero_in_middle:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.
  assert (H: n + 0 = n). {
    rewrite <- plus_n_O. reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Lemma zero_in_middle_2:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.
  rename n into x.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma add_assoc: 
  forall n m o,
  (n + m) + o = n + (m + o).
Proof.
  intros.
  induction n. 
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem zero_in_middle_3:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.
  assert (Hx := add_assoc n).
  rewrite Hx.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m.
Proof.
  intros n.
  intros m.
  intros.
  rewrite H.
  reflexivity.
Qed.

(* this is all thats needed for 7 and 9 *)

Theorem exercise3:
  forall n, n = 0 -> n + n = 0 + 0.
Proof.
  intros.
  assert (Ha := plus_id_example n 0).
  assert (Hb := Ha H).
  rewrite Hb.
  reflexivity.
Qed.
