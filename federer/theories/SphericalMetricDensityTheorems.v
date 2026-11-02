(** Federer (1969), 2.10.19(3)–(5), p. 181: lower measure comparison on open
    sets, zero density off a finite measurable set, and upper restricted
    density at most one almost everywhere. The auxiliary weak covering
    quotient handles zero costs; these statements retain the original
    positive-radius metric densities and Federer's finite-set conclusions at
    integer degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel MetricDensities MetricDensityNumericalBounds
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost SphericalEnlargementUP SphericalEnlargement
  SphericalMetricDensityComparison WeakCaratheodoryEnlargementDensityBound WeakCaratheodoryOffSetUpperDensity
  WeakCaratheodoryRestrictedDensity WeakCaratheodoryDensityQuotient CaratheodoryDensityUpperBound
  CoveringRelationLimits PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_19_3]: direct integer-degree open-set
    comparison of 2.10.19(3), p. 181 Retain the printed strict density bound
    and closed-set measurability. A nonpositive finite threshold is handled
    directly. *)
Theorem federer_2_10_19_3 (R : realType) (X : metricType R) (m : nat)
    (mu : set X -> \bar R) (B V : set X) (t : R) :
  is_measure mu -> (forall S : set X, closed S -> measure_measurable mu S) ->
  open V -> B `<=` V -> (forall x, B x -> t%:E<upper_metric_density m mu x) ->
  t%:E*spherical_measure m B<=mu V.
Proof.
move=> hm hclosedmeas ho hBV hlim.
have hpm := @spherical_measure_is_measure R X m.
case: (ltP 0%R t)=> [ht|ht].
- have hE := @spherical_enlargement_specification R X m.
  have hpsi := @spherical_measure_specification R X m.
  have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
    exact: positive_metric_closed_ball_closed hS.
  have hmeas (S : set X) (hS : is_positive_metric_closed_ball S) : measure_measurable mu S.
    exact: hclosedmeas S (hclosed S hS).
  apply: (@weak_caratheodory_enlargement_density_bound R X
    (@is_positive_metric_closed_ball R X) (@hausdorff_diameter_cost R X m) mu (spherical_measure m)
    (@spherical_enlargement R X m) (spherical_enlargement_control R m) B V t
    hE hm hpsi hclosed hmeas ho hBV ht)=> x hx.
  exact: lt_le_trans (hlim x hx) (@spherical_metric_density_le_covering_upper R X m mu x hm).
- have htE : t%:E<=0 by rewrite lee_fin.
  have hh := lee_wpmul2r (@measure_nonnegative R X (spherical_measure m) hpm B) htE.
  rewrite mul0e in hh; exact: le_trans hh (@measure_nonnegative R X mu hm V).
Qed.

(** Source for [federer_2_10_19_4]: direct integer-degree full zero-density
    limit in 2.10.19(4), p. 181. *)
Theorem federer_2_10_19_4 (R : realType) (X : metricType R) (m : nat)
    (mu : set X -> \bar R) (A : set X) :
  is_measure mu -> is_borel_regular_measure mu -> measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on (spherical_measure m) (~` A)
    [set x | partial_function_graph (metric_density m (measure_restrict mu A)) x 0].
Proof.
move=> hm hr hA hAf.
have hpm := @spherical_measure_is_measure R X m.
have hE := @spherical_enlargement_specification R X m.
have hpsi := @spherical_measure_specification R X m.
have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
  exact: positive_metric_closed_ball_closed hS.
have hmeas (S : set X) (hS : is_positive_metric_closed_ball S) : measure_measurable mu S.
  exact: (@borel_regular_borel_measurable R X mu hm hr S (closed_borel_set (hclosed S hS))).
have hae := @weak_caratheodory_off_set_upper_density R X (@is_positive_metric_closed_ball R X)
  (@hausdorff_diameter_cost R X m) mu (spherical_measure m) (@spherical_enlargement R X m)
  (spherical_enlargement_control R m) A hE hm hr hpsi hclosed hmeas hA hAf.
have hmu := measure_restrict_is_measure hm A.
apply: (@measure_null_subset R X (spherical_measure m) hpm _ _ _ hae)=> x [hnA hnot].
split=> // hup; apply: hnot.
have hu : upper_metric_density m (measure_restrict mu A) x<=0 :=
  le_trans (@spherical_metric_density_le_covering_upper R X m (measure_restrict mu A) x hmu) hup.
have [hl0 hu0] := @metric_densities_nonnegative R X m (measure_restrict mu A) x hmu.
have horder := @metric_densities_ordered R X m (measure_restrict mu A) x.
have hue : upper_metric_density m (measure_restrict mu A) x=0 by apply/eqP; rewrite eq_le hu hu0.
have hle : lower_metric_density m (measure_restrict mu A) x=0.
  apply/eqP; rewrite eq_le hl0 andbT; exact: le_trans horder hu.
by rewrite /metric_density /=; split.
Qed.

(** Source for [federer_2_10_19_5]: direct integer-degree upper-density
    bound in 2.10.19(5), p. 181 Only spherical measure of A is finite. A
    need not be measurable and the conclusion holds on all X. *)
Theorem federer_2_10_19_5 (R : realType) (X : metricType R) (m : nat) (A : set X) :
  spherical_measure m A < +oo -> measure_almost_everywhere (spherical_measure m)
    [set x | upper_metric_density m (measure_restrict (spherical_measure m) A) x<=1].
Proof.
move=> hAf.
have hpm := @spherical_measure_is_measure R X m.
have hE := @spherical_enlargement_specification R X m.
have hpsi := @spherical_measure_specification R X m.
have hclosed (S : set X) (hS : is_positive_metric_closed_ball S) : closed S.
  exact: positive_metric_closed_ball_closed hS.
have hae := @weak_caratheodory_restricted_upper_density R X (@is_positive_metric_closed_ball R X)
  (@hausdorff_diameter_cost R X m) (spherical_measure m) (@spherical_enlargement R X m)
  (spherical_enlargement_control R m) A hE hpsi hclosed hAf.
apply: (@measure_almost_everywhere_mono R X (spherical_measure m) hpm _ _ _ hae)=> x hx.
change (upper_metric_density m (measure_restrict (spherical_measure m) A) x<=1).
exact: le_trans (@spherical_metric_density_le_covering_upper R X m
  (measure_restrict (spherical_measure m) A) x (measure_restrict_is_measure hpm A)) hx.
Qed.
