(** Federer (1969), 3.3.16, p. 299: every original
    projected volume is bounded by actual Gross outer mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  ProjectionMeasure ProjectedVolumeGauge BorelCaratheodoryMeasure BorelRegularMeasureUP
  MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_original_projection_bound]: supporting
    replacement comparison in Federer 3.3.16, p. 299, from the
    actual gauge of 2.10.4(1), p. 172, and the Borel cost lower
    bound of 2.10.8, p. 175. An actual equal-mass Borel hull
    retains EVERY original subset A. No Hausdorff mass premise
    or universal Hausdorff/Gross comparability is assumed. *)
Theorem gross_original_projection_bound (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  euclidean_lebesgue_measure m (euclidean_projection_linear p @` A)<=@gross_measure R n m A.
Proof.
have [B [hAB [hB hMass]]]:=borel_regular_cover (@gross_measure_borel_regular R n m hmn) A.
rewrite hMass.
apply:le_trans (@measure_mono R _ _ (euclidean_lebesgue_is_measure R m)
  (euclidean_projection_linear p @` A) (euclidean_projection_linear p @` B) _ ) _.
- by move=>y [x hx <-]; exists x; last by []; exact:hAB x hx.
- apply:le_trans (@projected_volume_gauge_projection_bound R n m B
    (euclidean_projection_linear p) (euclidean_projection_linear_member p)) _.
  exact:(@borel_caratheodory_cost_bound R
    (inner_metric_space (@euclidean_inner_productP R n)) (@projected_volume_gauge R n m)
    (@projected_volume_gauge_borel_cover_cost R n m hmn) B hB).
Qed.
