(** The original section-coefficient integrals in Federer
    (1969), 3.2.45, p. 279, obtained from Fubini
    and finite interpolation of actual tube volumes. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps EuclideanBlockCoordinates VectorSetSum EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanBlockSetIntegral CompactConvexBlockSections CompactConvexBallSumPolynomial EuclideanVerticalBallSumSections
  EuclideanPrefixBallSums FinitePowerEvaluationUP EuclideanSectionCoefficientIntegral
  IntegralGeometricGauge EuclideanBallVolume MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  TopologicalBorel RealMetricBackground SummableRealFunctionUP PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_section_coefficient_integral]: supporting
    coefficient integral in the first polynomial display
    of Federer 3.2.45, p. 279. For each of
    finitely many positive radii, the actual compact
    vertical-ball sum is measurable and finite. Fubini,
    2.6.2(3), p. 115, gives the integral of its
    actual section-tube volumes. The proved pointwise
    section polynomial and finite inverse interpolation
    give the integrals of the original intrinsic
    coefficients. Empty fibres have zero coefficients;
    thin fibres and both empty coordinate blocks remain.
    No fibre measurability or target coefficient bound
    is supplied as a premise. *)
Theorem compact_convex_section_coefficient_integral (R : realType) m q
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q))))
    (E G : {linear R_n R (m+q).+1 -> R_n R (m+q).+1}) :
  K !=set0 -> compact K -> is_inner_convex K ->
  is_finite_power_evaluation E -> cancel E G ->
  let C := fun y : inner_metric_space (@euclidean_inner_productP R m) =>
    [ffun i : 'I_(m+q).+1 => if (i<=q)%N then
      fine (@integral_geometric_gauge R q (q-i) (leq_subr i q) 1
        [set z | K (@euclidean_block_join R m q (y,z))])*euclidean_unit_ball_volume R i else 0] in
  let V : R_n R (m+q).+1 := [ffun j : 'I_(m+q).+1 =>
    fine (@euclidean_lebesgue_measure R (m+q) (vector_set_sum K
      ((@euclidean_diagonal_map R (m+q) (fun l => if (l<m)%N then 0 else 1)) @`
        [set x | inner_norm (@euclidean_inner_productP R (m+q)) x<=j.+1%:R])))] in
  forall i, is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun y => C y i)) (G V i)%:E.
Proof.
move=> hNonempty hCompact hConvex hEvaluation hInverse C V.
pose N := (m+q)%N.
pose Z := inner_metric_space (@euclidean_inner_productP R N).
pose S := fun j : 'I_N.+1 => vector_set_sum K
  ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then 0 else 1)) @`
    [set x : Z | inner_norm (@euclidean_inner_productP R N) x<=j.+1%:R]).
have hSCompact j : @compact Z (S j).
  exact: (@euclidean_prefix_ball_sum_geometry R N m K 0 j.+1%:R
    hNonempty hCompact hConvex (ltW (ltr0n R j.+1))).2.1.
have hMeasurable j : measure_measurable (@euclidean_lebesgue_measure R N) (S j).
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R Z) (hSCompact j).
have hFinite j : (@euclidean_lebesgue_measure R N (S j)< +oo)%E := euclidean_compact_finite (hSCompact j).
have hSections y j : @euclidean_lebesgue_measure R q
    [set z | S j (@euclidean_block_join R m q (y,z))]=(E (C y) j)%:E.
  rewrite /S euclidean_vertical_ball_sum_section.
  have hPolynomial := @compact_convex_ball_sum_padded_polynomial R q N (leq_addl m q)
    [set z | K (@euclidean_block_join R m q (y,z))] j.+1%:R
    (@euclidean_block_section_compact R m q K y hCompact)
    (@euclidean_block_section_inner_convex R m q K y hConvex) (ltr0n R j.+1).
  rewrite hPolynomial; congr (_%:E); rewrite hEvaluation.
  apply: eq_bigr=> i _; by rewrite /C ffunE.
exact: (@euclidean_section_coefficient_integral R m q E G C S hInverse hMeasurable hFinite hSections).
Qed.
