(** Supporting localisation in Federer (1969), 2.9.21, p. 166: derivative
    values on interior points do not depend on curve values outside [a,b].
    The derivative is the actual two-sided quotient limit of 2.9.19, pp.
    163–165. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_derivative_neighbourhood_agreement]: supporting
    locality of the derivative used in Federer 2.9.21, p. 166, from its
    quotient definition in 2.9.19, p. 163 A common positive cutoff preserves
    the actual two-sided derivative under neighbourhood agreement. *)
Lemma real_derivative_neighbourhood_agreement (R : realType) (g h : R -> R)
    (x d v : R) : 0<d ->
  (forall y, `|y-x|<d -> g y=h y) ->
  has_real_curve_derivative g x v -> has_real_curve_derivative h x v.
Proof.
move=> hd he hD e heps; have [r [hr hcut]] := hD e heps.
exists (Num.min d r); split; first by rewrite lt_min hd hr.
move=> t /andP[ht0 htSmall].
have hmd : Num.min d r<=d by rewrite ge_min lexx.
have hmr : Num.min d r<=r by rewrite ge_min lexx orbT.
have htD : `|t|<d := lt_le_trans htSmall hmd.
have htR : `|t|<r := lt_le_trans htSmall hmr.
have hx : g x=h x by apply: he; rewrite subrr normr0.
have hxt : g (x+t)=h (x+t).
  apply: he; by rewrite addrAC subrr add0r.
rewrite -hxt -hx; apply: hcut; by apply/andP; split.
Qed.

(** Source for [real_derivative_segment_interior_agreement]: supporting
    localisation in Federer 2.9.21, p. 166 Curves agreeing on [a,b] have
    identical actual derivative graphs at every interior point, without
    asserting endpoint derivatives or global curve agreement. *)
Lemma real_derivative_segment_interior_agreement (R : realType) (g h : R -> R)
    (a b x v : R) :
  (forall y, a<=y -> y<=b -> g y=h y) -> a<x -> x<b ->
  (has_real_curve_derivative g x v <-> has_real_curve_derivative h x v).
Proof.
move=> he hax hxb.
pose d := Num.min (x-a) (b-x).
have hd : 0<d by rewrite /d lt_min !subr_gt0 hax hxb.
have hda : d<=x-a by rewrite /d ge_min lexx.
have hdb : d<=b-x by rewrite /d ge_min lexx orbT.
have hLocal y : `|y-x|<d -> g y=h y.
  rewrite ltr_norml=> /andP[hy1 hy2]; apply: he; lra.
split.
- exact: real_derivative_neighbourhood_agreement hd hLocal.
- apply: real_derivative_neighbourhood_agreement hd _=> y hy.
  exact: esym (hLocal y hy).
Qed.
