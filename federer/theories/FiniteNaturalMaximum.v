(** Federer (1969), 3.4.8(14), pp. 328, 336:
    a nonempty finite component family attains its maximum
    natural dimension. This supporting connection specializes the
    existing finite preorder maximum theorem to natural values. *)
From mathcomp Require Import all_boot boolp.
From Federer Require Import FinitePreorderMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [finite_natural_maximum]: attain the component
    supremum in 3.4.8(14), pp. 328, 336.
    Repetitions in the finite list are allowed. *)
Theorem finite_natural_maximum (X:choiceType) (F:seq X) (f:X->nat):
  F!=[::] ->exists x,x \in F /\forall y,y \in F ->(f y<=f x)%N.
Proof.
move=>hNonempty.
pose pre:=fun x y=>is_true (f x<=f y)%N.
have hReflexive x:pre x x:=leqnn (f x).
have hTransitive x y z:pre x y ->pre y z ->pre x z.
  move=>hXY hYZ;exact:leq_trans hXY hYZ.
have [x [hX hMaximum]]:=@finite_preorder_maximal_member X pre hReflexive hTransitive F hNonempty.
exists x;split;first exact:hX.
move=>y hY.
have /orP [hYX|hXY]:=leq_total (f y) (f x).
- exact:hYX.
- exact:hMaximum y hY hXY.
Qed.
