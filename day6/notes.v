Lemma and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  -reflexivity.
  -reflexivity.
Qed.

Lemma and_in_conj : 
  forall x y,
  3 + x = y /\ 2 * 2 = x -> x = 4 /\ y = 7.
Proof.
  intros.
  destruct H.
  simpl in *.
  apply conj.
  - rewrite H0. reflexivity.
  - rewrite <- H0 in H. rewrite <- H. reflexivity.
Qed.

Lemma or_example : 
  forall x, x = 2 -> x = 2 \/ x = 3.
Proof.

  (*
  apply or_introl
  assumption
  *)

  intros.
  left.
  assumption.
Qed.