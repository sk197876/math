(** Federer (1969), 3.1.11, pp. 220–221:
    a cellwise estimate for integrating the derivative
    of a normed-vector curve. This is the fundamental
    theorem step in the repeated integration-by-parts proof
    of the Taylor formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP InnerConvex NormDifferentialUP
  NormDifferentialLinear NormDifferentialSubtraction NormDifferentialConvexBound
  NormHigherCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_closed_interval_inner_convex]:
    scalar intervals are convex, supporting the
    derivative bound in the Taylor proof of Federer
    3.1.11, pp. 220–221. *)
Lemma scalar_closed_interval_inner_convex (R : realType) (p q : R) :
  @is_inner_convex R R^o (fun s=>p<=s<=q).
Proof.
move=> x y /andP [hpx hxq] /andP [hpy hyq] t ht0 ht1.
have ht : 0<= 1-t by rewrite subr_ge0.
change (is_true (p<=(1-t)*x+t*y<=q)).
apply/andP; split.
- have h1 := ler_wpM2l ht hpx.
  have h2 := ler_wpM2l ht0 hpy; nra.
- have h1 := ler_wpM2l ht hxq.
  have h2 := ler_wpM2l ht0 hyq; nra.
Qed.

(** Source for [scalar_coefficient_linear_bound]:
    boundedness of the real-source linear map t to
    t v, supporting the integral proof in Federer
    3.1.11, pp. 220–221. *)
Lemma scalar_coefficient_linear_bound (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (v : Y) :
  norm_bounded_linear (fun t : R^o=>`|t|) NY (scalar_coefficient_linear_map v).
Proof.
exists (NY v); split; first exact (real_seminorm_nonnegative hNY.1 v).
move=> t; change (NY (t*:v)<=NY v*`|t|).
by rewrite (real_seminorm_scale hNY.1) mulrC.
Qed.

(** Source for [normed_primitive_cell_estimate]:
    if the derivative differs from its tagged value
    by at most e throughout a cell, its integral
    increment differs from the tagged linear increment by
    at most e times the cell length. This supports
    the Taylor integral in Federer 3.1.11, pp. 220–221. *)
Theorem normed_primitive_cell_estimate (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (F D : R->Y) (p q u e : R) :
  p<=u -> u<=q -> 0<=e ->
  (forall s, p<=s<=q ->
    has_norm_differential (fun t : R^o=>`|t|) NY A F s
      (scalar_coefficient_linear_map (D s))) ->
  (forall s, p<=s<=q -> NY (D s-D u)<=e) ->
  NY ((q-p)*:D u-(F q-F p))<=e*(q-p).
Proof.
move=> hpu huq he hD hosc.
pose L := scalar_coefficient_linear_map (D u).
pose G s := F s-L s.
have hG s (hs : p<=s<=q) : exists M : Hom R^o Y,
    has_norm_differential (fun t : R^o=>`|t|) NY A G s M /\
    forall t, NY (M t)<=e*`|t|.
  pose M := scalar_coefficient_linear_map (D s)-L.
  exists M; split.
  - apply: (norm_differential_subtract (@scalar_absolute_value_norm R) hNY (hD s hs)).
    exact (norm_differential_linear (@scalar_absolute_value_norm R) hNY
      (norm_differential_interior (hD s hs)) (scalar_coefficient_linear_bound hNY (D u))).
  - move=> t; change (NY (t*:D s-t*:D u)<=e*`|t|).
    rewrite -scalerBr (real_seminorm_scale hNY.1) mulrC.
    exact (ler_wpM2r (normr_ge0 t) (hosc s hs)).
have hpq : p<=q := le_trans hpu huq.
have hpp : p<=p<=q by rewrite lexx hpq.
have hqq : p<=q<=q by rewrite lexx hpq.
have hbound := @norm_differential_convex_bound R R^o Y
  (fun t : R^o=>`|t|) NY (@scalar_absolute_value_norm R) hNY A
  (fun s=>p<=s<=q) G e (@scalar_closed_interval_inner_convex R p q) he hG q p hqq hpp.
have hid : G q-G p=(F q-F p)-(q-p)*:D u.
  change (F q-q*:D u-(F p-p*:D u)=(F q-F p)-(q-p)*:D u).
  by rewrite scalerBl !opprD !opprK addrACA.
have hqp0 : 0<=q-p by rewrite subr_ge0.
rewrite hid (ger0_norm hqp0) in hbound.
by rewrite (real_seminorm_subtract hNY.1).
Qed.
