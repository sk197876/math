(** Federer (1969), 2.10.47(1), pp. 204–205: the second cutoff comparison
    transfers Hausdorff-null coordinate sections to gamma_i-null sections.
    State the transfer for every null set in the root cube, with positive
    real degree and explicit coefficient. Source context:
    DyadicContentCutoffUpper.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric DyadicCubeGridUP DyadicCubeGrid
  DyadicScaleBounds DyadicContentCutoffUpper RefiningCoverContent
  MetricRealPowerCost MetricRealPowerMeasureUP MetricDiameter HausdorffLengthUP
  MetricScaleEnvelope MetricScaleCutoffCost CaratheodoryLimitUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_content_null_set]: supporting nullity
    transfer used in 2.10.47(1), pp. 204–205.
    The null set need not be measurable or compact. *)
Theorem dyadic_content_null_set (R : realType) n (a : R_n R n) Q c p i gamma
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<=c)%R -> (0<p)%R ->
  (forall x, S x -> forall l, (a l<=x l<=a l+1)%R) -> mu S=0 -> gamma S=0.
Proof.
move=> hQ hg hmu hn hc hp hS hz.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose nu := metric_scale_envelope (fun T : @nonempty_metric_sets R X=>val T)
  (fun T=>metric_real_diameter_cost c p (val T)) (((2^i)%N)%:R^-1)%:E.
have hnu := metric_scale_envelope_specification (fun T : @nonempty_metric_sets R X=>val T)
  (fun T=>metric_real_diameter_cost c p (val T)) (((2^i)%N)%:R^-1)%:E.
have hcost (T : set X) : 0<=metric_real_diameter_cost c p T :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter T) hc.
have hnm := metric_scale_envelope_is_measure hnu (fun T=>hcost (val T)).
have hgm := refining_cover_content_measure hg (fun T _=>hcost T).
have hupper := @caratheodory_limit_upper R X _ _ _ mu hmu S
  (((2^i)%N)%:R^-1)%:E nu (dyadic_side_positive R i) hnu.
have hnz : nu S=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hnm) andbT; by rewrite -hz.
have hb := @dyadic_power_content_cutoff_upper_bound R n a Q c p i gamma nu hQ hg hnu hn hc hp S hS.
rewrite hnz mule0 in hb; apply/eqP; by rewrite eq_le hb (measure_nonnegative hgm).
Qed.
