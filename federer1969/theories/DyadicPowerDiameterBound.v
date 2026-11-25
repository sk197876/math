(** Federer (1969), 2.10.47, p. 204: compare the dyadic cover cost with the
    original diameter cost. For positive diameter use the adjacent dyadic
    scale; for zero diameter use arbitrarily fine cubes. The coefficient is
    2^n (2 sqrt(n))^p, equal to the printed coefficient for nonnegative real
    p. A positive coefficient c of the gauge stays explicit. Source context:
    DyadicPowerContentBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicScaleBounds DyadicPowerZeroBound DyadicPowerContentBound
  RefiningCoverContent MetricDiameter MetricRealPowerCost RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_power_content_diameter_bound]: the
    single-generator estimate behind the second comparison
    in 2.10.47, p. 204, with a finite real
    diameter r. Positive real exponents are covered;
    the zero-diameter case is included explicitly. *)
Theorem dyadic_power_content_diameter_bound (R : realType) n (a : R_n R n) Q c p i gamma
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  (0<=c)%R -> (0<p)%R -> S!=set0 ->
  (forall x, S x -> forall l, (a l<=x l<=a l+1)%R) ->
  extended_metric_diameter S=r%:E -> (0<=r<=((2^i)%N)%:R^-1)%R ->
  gamma S<=(((2^n)%N)%:R*real_power (2*Num.sqrt n%:R) p*(c*real_power r p))%:E.
Proof.
move=> hQ hg hc hp hne hroot hdiam /andP [hr hri].
have h2n : (0<=((2^n)%N)%:R :> R)%R by rewrite ler0n.
have hs : (0<=Num.sqrt (n%:R : R))%R := sqrtr_ge0 _.
case: (eqVneq r 0%R)=> [hr0|hr0].
- rewrite hr0 real_power_zero_base ?gt_eqF // !mulr0.
  apply: (@dyadic_power_bounds_force_zero R
    (((2^n)%N)%:R*c*real_power (Num.sqrt n%:R) p)%R p i _ _ hp).
  + exact: mulr_ge0 (mulr_ge0 h2n hc) (real_power_nonnegative _ _).
  + move=> j hij.
    have hd : extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E.
      by rewrite hdiam hr0 lee_fin; exact: ltW (dyadic_side_positive R j).
    have hh := @dyadic_power_content_level_bound R n a Q c p i gamma j S hQ hg hc (ltW hp) hij hne hroot hd.
    rewrite (@real_power_product R (Num.sqrt n%:R) (((2^j)%N)%:R^-1) p hs (ltW (dyadic_side_positive R j))) !mulrA in hh.
    exact hh.
- have hrpos : (0<r)%R by rewrite lt_def hr0 hr.
  have [j [hij hlow hhigh]] := @dyadic_scale_bracket R i r hrpos hri.
  have hd : extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E by rewrite hdiam lee_fin.
  apply: le_trans (@dyadic_power_content_level_bound R n a Q c p i gamma j S hQ hg hc (ltW hp) hij hne hroot hd) _.
  rewrite lee_fin.
  have hside : ((((2^j)%N)%:R^-1 : R)<=2*r)%R.
    rewrite dyadic_side_successor in hlow; lra.
  have hbase : (Num.sqrt n%:R/((2^j)%N)%:R<=(2*Num.sqrt n%:R)*r)%R.
    have hh := ler_wpM2l hs hside; by rewrite mulrCA mulrA in hh.
  have hpw := real_power_monotone (mulr_ge0 hs (ltW (dyadic_side_positive R j))) hbase hp.
  rewrite (@real_power_product R (2*Num.sqrt n%:R) r p (mulr_ge0 (ler0n R 2) hs) hr) in hpw.
  have hh := ler_wpM2l h2n (ler_wpM2l hc hpw).
  apply: le_trans hh _; rewrite !mulrA [(((2^n)%N)%:R*c*real_power (2*Num.sqrt n%:R) p)%R]mulrAC.
  exact: lexx.
Qed.
