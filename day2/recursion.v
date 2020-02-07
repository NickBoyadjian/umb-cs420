Compute S (S 9).

Fixpoint add (n1:nat) (n2:nat) := (* we use fixpoint here because it's recursive *)
  match n1 with
    | 0 => n2
    | S n => S (add n n2)
end.

Compute add 0 (S (S 0)).

Fixpoint evenb (n:nat) :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => evenb n'
  end.

Compute evenb 24. 
