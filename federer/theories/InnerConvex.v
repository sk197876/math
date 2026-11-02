(** Federer (1969), 1.7.13, p. 37: convexity and the midpoint used in the
    closest-point proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_inner_convex]: Federer 1.7.13, p. 37,
    the hypothesis that C is convex: it contains each segment
    joining two of its points. This specification is independent
    of a choice of generators or a convex-hull construction. *)
Definition is_inner_convex (R : realFieldType) (V : lmodType R)
    (C : set V) : Prop :=
  forall x y, C x -> C y -> forall t : R, 0 <= t -> t <= 1 ->
    C ((1-t) *: x + t *: y).

(** Source for [inner_convex_midpoint]: Federer 1.7.13,
    p. 37, first observation in the diameter estimate:
    (x+y)/2 belongs to C when x and y do. *)
Lemma inner_convex_midpoint (R : realFieldType) (V : lmodType R)
    (C : set V) (hC : is_inner_convex C) x y :
    C x -> C y -> C ((2 : R)^-1 *: (x+y)).
Proof.
move=> hx hy.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
have hi : 0 <= (2 : R)^-1 by rewrite invr_ge0 ler0n.
have hil : (2 : R)^-1 <= 1 by rewrite invf_le1 ?ler1n // ltr0n.
have he : 1-(2 : R)^-1 = (2 : R)^-1.
  apply: (mulfI h2); rewrite mulrBr mulr1 mulfV // .
  change (1 + 1 - 1 = 1 :> R); by rewrite addrK.
move: (hC x y hx hy _ hi hil); by rewrite he -scalerDr.
Qed.
