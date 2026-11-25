(** Federer (1969), 3.2.11, p. 249: apply
    2.10.25 to the last-coordinate projection on a perturbed
    fibre. The target Euclidean properness and unit Lipschitz
    bound are proved from the existing interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanMetricProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanLebesgueDimensions EuclideanHausdorffLebesgue
  MetricCartesianProductUP LipschitzUP HausdorffMeasure HausdorffFibreCost HausdorffFibreCutoffs
  HausdorffFibreIntegralBound EuclideanBallVolume CoareaNullFibres MappingMultiplicity
  MeasureIntegralBounds PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_projection_fibre_coefficient_positive]:
    the positive geometric coefficient in Federer 3.2.11,
    p. 249. This is the reciprocal of the displayed
    c when k=m-n, expressed through the already proved
    2.10.25 coefficient at unit Lipschitz bound. *)
Lemma coarea_projection_fibre_coefficient_positive (R:realType) k n:
  (0<hausdorff_fibre_bound_constant k n (1:R))%R.
Proof.
rewrite /hausdorff_fibre_bound_constant expr1n mul1r.
apply:divr_gt0; last exact (euclidean_unit_ball_volumeE R (k+n)).2.
exact (mulr_gt0 (euclidean_unit_ball_volumeE R k).2 (euclidean_unit_ball_volumeE R n).2).
Qed.

(** Source for [coarea_projection_fibre_upper_bound]: the
    projection-slicing inequality in the critical case of
    Federer 3.2.11, p. 249. The source set S may
    be any perturbed fibre and need not be measurable or
    have finite Hausdorff mass; the upper integral is retained. *)
Theorem coarea_projection_fibre_upper_bound (R:realType) m n k
    (S:set (R_n R (m+n))):
  measure_upper_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (m+n))) k
      (mapping_fibre (@euclidean_last_block R m n) S z):extended_real_line R)))<=
  (hausdorff_fibre_bound_constant k n (1:R))%:E *
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) (k+n) S.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose p:=fun x:X=>(@euclidean_last_block R m n x:Y).
have hP:is_metric_lipschitz_bound setT p (1:R).
  exact (metric_product_second_nonexpanding (@euclidean_blocks_are_metric_product R m n)).
have hCondition:hausdorff_fibre_integral_condition p S k n.
  right; exact (@coarea_euclidean_source_proper R n).
have hBound:=@hausdorff_lipschitz_fibre_integral_bound R X Y p 1%R k n S hP hCondition.
have hTarget:(@hausdorff_measure R Y n)=(@euclidean_lebesgue_measure R n).
  apply:funext=>A; exact (euclidean_hausdorff_spherical_lebesgue A).1.
rewrite hTarget in hBound.
exact hBound.
Qed.
