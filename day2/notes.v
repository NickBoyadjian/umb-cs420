Definition andb (b1:bool) (b2:bool) :=
  match b1 with
  | true  => b2
  | false => false
  end.

Definition nandb (b1:bool) (b2:bool) :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
  simpl.        (* simplifies the left hand side *)
  reflexivity.  (* checks if both sides are equal *)
Qed.

Inductive rgb :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition r := red.

Compute (primary red).

Definition C1 := primary red.

Definition rgb_inverse (r:rgb) : rgb :=
  match r with
  | red => blue
  | green => red
  | blue => green
end.

Definition color_inverse c :=
  match c with
    | black => white
    | white => black
    | primary r => primary (rgb_inverse r)
end.

Compute color_inverse C1.



















