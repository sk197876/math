(** Federer (1969), 2.10.47, p. 204: the second
    cutoff comparison on subsets of the root cube.
    Replace every small generator by its intersection
    with the cube, cover it by at most 2^n finer
    cubes, and sum the power-cost bound before taking
    the covering infimum. Positive real degrees are
    allowed with an explicit nonnegative coefficient c.
    The bound includes zero-diameter generators. Source
    editions: DyadicPowerDiameterBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicScaleBounds DyadicPowerDiameterBound RefiningCoverContent
  MetricDiameterUP MetricDiameter MetricRealPowerCost RealPower HausdorffLengthUP
  MetricScaleEnvelopeUP MetricScaleWeightedBound MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_power_content_cutoff_upper_bound]: the
    upper comparison gamma_i(E)<=2^n(2 sqrt(n))^p
    phi_(2^-i)(E) in 2.10.47, p. 204,
    for positive ambient dimension and real degree.
    E need not be measurable or compact. *)
Theorem dyadic_power_content_cutoff_upper_bound (R : realType) n (a : R_n R n) Q c p i gamma nu :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  is_metric_scale_envelope (fun S : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>val S)
    (fun S=>metric_real_diameter_cost c p (val S)) (((2^i)%N)%:R^-1)%:E nu ->
  (0<n)%N -> (0<=c)%R -> (0<p)%R ->
  forall E : set (inner_metric_space (@euclidean_inner_productP R n)), (forall x, E x -> forall l, (a l<=x l<=a l+1)%R) ->
  gamma E<=( ((2^n)%N)%:R*real_power (2*Num.sqrt n%:R) p)%:E*nu E.
Proof.
move=> hQ hg hn hnpos hc hp.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose C := [set x : X | forall l, (a l<=x l<=a l+1)%R].
pose K : R := (((2^n)%N)%:R*real_power (2*Num.sqrt n%:R) p)%R.
have hK : (0<K)%R.
  apply: mulr_gt0; first by rewrite ltr0n expn_gt0.
  apply: real_power_strictly_positive; apply: mulr_gt0; first by rewrite ltr0n.
  by rewrite sqrtr_gt0 ltr0n.
have hcost (S : set X) : 0<=metric_real_diameter_cost c p S := @metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) hc.
have hm := refining_cover_content_measure hg (fun S _=>hcost S).
have hgen (S : @nonempty_metric_sets R X) :
    extended_metric_diameter (val S)<=(((2^i)%N)%:R^-1)%:E ->
    measure_restrict gamma C (val S)<=K%:E*metric_real_diameter_cost c p (val S).
  move=> hdS; pose T := C `&` val S.
  case: (pselect (T!=set0))=> [hne|hempty].
  - have hdT : extended_metric_diameter T<=extended_metric_diameter (val S).
      apply: extended_metric_diameter_mono=> x hx; exact hx.2.
    have hdiam := le_trans hdT hdS.
    have hnon := metric_diameter_nonnegative (extended_metric_diameter_specification T).
    have hfin : extended_metric_diameter T \is a fin_num.
      rewrite (ge0_fin_numE hnon); exact: le_lt_trans hdiam (ltry _).
    pose r := fine (extended_metric_diameter T).
    have hrE : extended_metric_diameter T=r%:E := esym (fineK hfin).
    have hr : (0<=r)%R by rewrite hrE lee_fin in hnon.
    have hri : (r<=((2^i)%N)%:R^-1)%R by rewrite hrE lee_fin in hdiam.
    have hb := @dyadic_power_content_diameter_bound R n a Q c p i gamma T r hQ hg hc hp hne
      (fun x hx=>hx.1) hrE (ltac:(by apply/andP)).
    change (gamma T<=K%:E*metric_real_diameter_cost c p (val S)).
    have hvalue : (K*(c*real_power r p))%:E=K%:E*metric_real_diameter_cost c p T.
      by rewrite /metric_real_diameter_cost hrE metric_real_power_cost_finite EFinM.
    rewrite hvalue in hb; apply: le_trans hb _.
    apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW hK.
    exact: metric_real_power_cost_monotone hc (ltW hp) hnon hdT.
  - have he : T=set0 by apply/seteqP; split=> [x hx|x []]; apply: hempty; by exists x.
    change (gamma T<=K%:E*metric_real_diameter_cost c p (val S)); rewrite he (measure_empty hm).
    apply: mule_ge0; first by rewrite lee_fin; exact: ltW hK.
    exact: hcost.
move=> E hE.
have hh := @measure_bounded_by_scaled_metric_envelope R X _ _ _ _ nu
  (measure_restrict gamma C) K hn (measure_restrict_is_measure hm C) hK hgen E.
by rewrite (@measure_restrict_subset_value R X gamma C E hE) in hh.
Qed.
