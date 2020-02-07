Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m. (* if n = m then n + n = m + m *)
Proof.
  intros.
  rewrite H. (* all occurences of n become m because n = m *)
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed. 

(*
  we use destruct to get all possible values of a function
  destruct n.
  -
  -

  this bullets under destruct are used to tackle the individual sub goals
*)



Theorem plus_n_O : forall n:nat,
  n = n + 0.
Proof.
  intros.
  induction n.
  - reflexivity. (* n = 0 *)
  - rewrite IHn; reflexivity.
Qed.
