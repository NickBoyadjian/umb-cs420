Inductive natural :=
| zero: natural
| successor: natural -> natural.

Inductive pairnat :=
| make_pair: nat -> nat -> pairnat.

Compute make_pair 0 10.

Inductive lnat :=
| empty: lnat
| lpair: nat -> lnat -> lnat.

Inductive lnat2 :=
| empty2 : lnat2
| one: nat -> lnat2
| concat: lnat2 -> lnat2 -> lnat2.

Compute empty.
Compute (lpair 0).
Compute (lpair 10 (lpair 0 empty)).

Compute empty2.
Compute (one 0).
Compute (concat (one 0) (one 10)).