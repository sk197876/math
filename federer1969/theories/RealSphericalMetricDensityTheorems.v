(** Federer (1969), 2.10.19(3)–(5), p. 181: lower measure comparison on open
    sets, zero density off a finite measurable set, and upper restricted
    density at most one almost everywhere. The auxiliary weak covering
    quotient handles zero costs; these statements retain the original
    positive-radius metric densities and Federer's finite-set conclusions at
    every nonnegative real degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel RealMetricDensities RealMetricDensityLimits
  HausdorffMeasureUP RealHausdorffMeasure RealHausdorffMeasureLaws RealHausdorffNormalisation
  MetricRealPowerCost SphericalEnlargementUP SphericalEnlargement RealSphericalEnlargement
  RealSphericalMetricDensityComparison WeakCaratheodoryEnlargementDensityBound WeakCaratheodoryOffSetUpperDensity
  WeakCaratheodoryRestrictedDensity WeakCaratheodoryDensityQuotient CaratheodoryDensityUpperBound
  CoveringRelationLimits PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_19_3_real]: direct real-degree open-set
    comparison of 2.10.19(3), p. 181. Retain the printed strict density bound
    and closed-set measurability. A nonpositive finite threshold is handled
    directly. *)
Theorem federer_2_10_19_3_real (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (mu : set X -> \bar R) (B V : set X) (t : R) :
  is_measure mu -> (forall S : set X, closed S -> measure_measurable mu S) ->
  open V -> B `<=` V -> (forall x, B x -> t%:E<upper_real_metric_density hp mu x) ->
  t%:E*(@real_spherical_measure R X p hp) B<=mu V.
Proof.
move=> hm hclosedmeas ho hBV hlim.
have hpm := @real_spherical_measure_is_measure R X p hp.
case: (ltP 0%R t)=> [ht|ht].
- have hE := @real_spherical_enlargement_specification R X (real_hausdorff_normalisation hp) p
    (ltW (real_hausdorff_normalisation_positive hp)) hp.
  have hpsi := @real_spherical_measure_specification R X p hp.
  have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
    exact: positive_metric_closed_ball_closed hS.
  have hmeas (S : set X) (hS : is_positive_metric_closed_ball S) : measure_measurable mu S.
    exact: hclosedmeas S (hclosed S hS).
  apply: (@weak_caratheodory_enlargement_density_bound R X
    (@is_positive_metric_closed_ball R X) (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) mu ((@real_spherical_measure R X p hp))
    (@spherical_enlargement R X 1) (@real_spherical_enlargement_control R p) B V t
    hE hm hpsi hclosed hmeas ho hBV ht)=> x hx.
  exact: lt_le_trans (hlim x hx) (@real_spherical_metric_density_le_covering_upper R X p hp mu x hm).
- have htE : t%:E<=0 by rewrite lee_fin.
  have hh := lee_wpmul2r (@measure_nonnegative R X ((@real_spherical_measure R X p hp)) hpm B) htE.
  rewrite mul0e in hh; exact: le_trans hh (@measure_nonnegative R X mu hm V).
Qed.

(** Source for [federer_2_10_19_4_real]: direct real-degree full zero-density
    limit in 2.10.19(4), p. 181. *)
Theorem federer_2_10_19_4_real (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (mu : set X -> \bar R) (A : set X) :
  is_measure mu -> is_borel_regular_measure mu -> measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on ((@real_spherical_measure R X p hp)) (~` A)
    [set x | partial_function_graph (real_metric_density hp (measure_restrict mu A)) x 0].
Proof.
move=> hm hr hA hAf.
have hpm := @real_spherical_measure_is_measure R X p hp.
have hE := @real_spherical_enlargement_specification R X (real_hausdorff_normalisation hp) p
    (ltW (real_hausdorff_normalisation_positive hp)) hp.
have hpsi := @real_spherical_measure_specification R X p hp.
have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
  exact: positive_metric_closed_ball_closed hS.
have hmeas (S : set X) (hS : is_positive_metric_closed_ball S) : measure_measurable mu S.
  exact: (@borel_regular_borel_measurable R X mu hm hr S (closed_borel_set (hclosed S hS))).
have hae := @weak_caratheodory_off_set_upper_density R X (@is_positive_metric_closed_ball R X)
  (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) mu ((@real_spherical_measure R X p hp)) (@spherical_enlargement R X 1)
  (@real_spherical_enlargement_control R p) A hE hm hr hpsi hclosed hmeas hA hAf.
have hmu := measure_restrict_is_measure hm A.
apply: (@measure_null_subset R X ((@real_spherical_measure R X p hp)) hpm _ _ _ hae)=> x [hnA hnot].
split=> // hup; apply: hnot.
have hu : upper_real_metric_density hp (measure_restrict mu A) x<=0 :=
  le_trans (@real_spherical_metric_density_le_covering_upper R X p hp (measure_restrict mu A) x hmu) hup.
have [hl0 hu0] := @real_metric_densities_nonnegative R X p hp (measure_restrict mu A) x hmu.
have horder := @real_metric_densities_ordered R X p hp (measure_restrict mu A) x.
have hue : upper_real_metric_density hp (measure_restrict mu A) x=0 by apply/eqP; rewrite eq_le hu hu0.
have hle : lower_real_metric_density hp (measure_restrict mu A) x=0.
  apply/eqP; rewrite eq_le hl0 andbT; exact: le_trans horder hu.
by rewrite /real_metric_density /=; split.
Qed.

(** Source for [federer_2_10_19_5_real]: direct real-degree upper-density
    bound in 2.10.19(5), p. 181. Only spherical measure of A is finite. A
    need not be measurable and the conclusion holds on all X. *)
Theorem federer_2_10_19_5_real (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R) (A : set X) :
  (@real_spherical_measure R X p hp) A < +oo -> measure_almost_everywhere ((@real_spherical_measure R X p hp))
    [set x | upper_real_metric_density hp (measure_restrict ((@real_spherical_measure R X p hp)) A) x<=1].
Proof.
move=> hAf.
have hpm := @real_spherical_measure_is_measure R X p hp.
have hE := @real_spherical_enlargement_specification R X (real_hausdorff_normalisation hp) p
    (ltW (real_hausdorff_normalisation_positive hp)) hp.
have hpsi := @real_spherical_measure_specification R X p hp.
have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
  exact: positive_metric_closed_ball_closed hS.
have hae := @weak_caratheodory_restricted_upper_density R X (@is_positive_metric_closed_ball R X)
  (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) ((@real_spherical_measure R X p hp)) (@spherical_enlargement R X 1)
  (@real_spherical_enlargement_control R p) A hE hpsi hclosed hAf.
apply: (@measure_almost_everywhere_mono R X ((@real_spherical_measure R X p hp)) hpm _ _ _ hae)=> x hx.
change (upper_real_metric_density hp (measure_restrict ((@real_spherical_measure R X p hp)) A) x<=1).
exact: le_trans (@real_spherical_metric_density_le_covering_upper R X p hp
  (measure_restrict ((@real_spherical_measure R X p hp)) A) x (measure_restrict_is_measure hpm A)) hx.
Qed.
