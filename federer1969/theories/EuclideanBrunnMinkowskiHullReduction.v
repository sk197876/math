(** Federer (1969), 3.2.41, printed p. 278, final proof
    paragraph: reduce arbitrary original nonempty sets to the
    measurable case through their actual density-one hulls. This
    is a reduction lemma; its measurable-case argument remains a
    separate proof obligation and is not a project axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  CenteredBallRelations MeasureDensityPoints VectorSetSum EuclideanVectorSumVolume
  EuclideanDensityOneHull EuclideanDensityHullSum MeasureUP MeasureBasic
  ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_brunn_minkowski_hull_reduction]: supporting
    final passage in Federer 3.2.41, p. 278. Given the actual
    measurable-set inequality, it proves the whole arbitrary-set
    inequality, without adding source or sum measurability. Zero
    factors are handled through original-point translates, since
    their density-one hulls may be empty. Infinite volumes remain. *)
Theorem euclidean_brunn_minkowski_hull_reduction (R:realType) n:
  (0<n)%N ->
  (forall C D:set (inner_metric_space (@euclidean_inner_productP R n)),
    measure_measurable (@euclidean_lebesgue_measure R n) C ->
    measure_measurable (@euclidean_lebesgue_measure R n) D ->C !=set0 ->D !=set0 ->
    extended_positive_power (@euclidean_lebesgue_measure R n C) (n%:R)^-1+
      extended_positive_power (@euclidean_lebesgue_measure R n D) (n%:R)^-1<=
      extended_positive_power (@euclidean_lebesgue_measure R n (vector_set_sum C D)) (n%:R)^-1) ->
  forall A B:set (inner_metric_space (@euclidean_inner_productP R n)),
    A !=set0 ->B !=set0 ->
    extended_positive_power (@euclidean_lebesgue_measure R n A) (n%:R)^-1+
      extended_positive_power (@euclidean_lebesgue_measure R n B) (n%:R)^-1<=
      extended_positive_power (@euclidean_lebesgue_measure R n (vector_set_sum A B)) (n%:R)^-1.
Proof.
move=> hn hMeasurable A B hA hB.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose V:=@centered_closed_ball_relation R [the metricType R of E].
pose H:=fun C:set E=>measure_density_one_points mu V C.
have hm:=euclidean_lebesgue_is_measure R n.
change (extended_positive_power (mu A) (n%:R)^-1+
  extended_positive_power (mu B) (n%:R)^-1<=
  extended_positive_power (mu (vector_set_sum A B)) (n%:R)^-1).
have hp:(0<(n%:R:R)^-1)%R by rewrite invr_gt0 ltr0n.
case:(pselect (mu A=0))=>[hA0|hA0].
- rewrite hA0 (extended_positive_power_zero hp) add0e.
  exact:(@extended_positive_power_monotone R (mu B) (mu (vector_set_sum A B))
    (n%:R)^-1 (measure_nonnegative hm B)
    (@euclidean_vector_sum_volume_lower_right R n A B hA) hp).
case:(pselect (mu B=0))=>[hB0|hB0].
- rewrite hB0 (extended_positive_power_zero hp) adde0.
  exact:(@extended_positive_power_monotone R (mu A) (mu (vector_set_sum A B))
    (n%:R)^-1 (measure_nonnegative hm A)
    (@euclidean_vector_sum_volume_lower_left R n A B hB) hp).
have hHullNonempty (C:set E):mu C<>0 ->H C !=set0.
  move=> hC; apply:contrapT=> hEmpty.
  have hSet:H C=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x hx; apply:hEmpty; by exists x.
  have he:=@euclidean_density_one_hull_equal_volume R n C.
  change (mu C=mu (H C)) in he.
  apply:hC; by rewrite he hSet /mu (measure_empty hm).
have hCA:H A !=set0:=hHullNonempty A hA0.
have hCB:H B !=set0:=hHullNonempty B hB0.
have hPair:=hMeasurable (H A) (H B)
  (@euclidean_density_one_hull_measurable R n A)
  (@euclidean_density_one_hull_measurable R n B) hCA hCB.
rewrite -(@euclidean_density_one_hull_equal_volume R n A)
  -(@euclidean_density_one_hull_equal_volume R n B) in hPair.
have hSub:=@euclidean_density_one_hull_vector_sum R n A B.
have hVolume:=@measure_mono R E mu hm _ _ hSub.
rewrite /mu in hVolume.
rewrite -(@euclidean_density_one_hull_equal_volume R n (vector_set_sum A B)) in hVolume.
exact:(le_trans hPair (@extended_positive_power_monotone R _ _ (n%:R)^-1
  (measure_nonnegative hm _) hVolume hp)).
Qed.
