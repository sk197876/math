(** Original compact convex section inequality in Federer
    (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps EuclideanBlockCoordinates VectorSetSum EuclideanLebesgueDimensions EuclideanBallVolume
  IntegralGeometricGauge IntegralGeometricGaugeIndexEquality CompactConvexBlockSections CompactConvexBallSumPolynomial
  FinitePowerEvaluationExists CompactConvexSectionCoefficientIntegral CompactConvexSectionCoefficientComparison
  FiniteCoefficientIntegralUnscale MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureFiniteRealScaleIntegral
  RealMetricBackground SummableRealFunctionUP PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_intrinsic_section_comparison]: direct
    section inequality in Federer 3.2.45, p. 279,
    first for the original nonempty compact convex K.
    The actual intrinsic section function has a finite
    ordinary integral. Finite interpolation proves its
    integrability from Fubini; the independently proved
    anisotropic coefficient bounds give the stated upper
    bound after cancelling the positive original alpha
    coefficient. Empty and thin fibres and every degree
    k<=q are retained, including k=0 and m=0.
    Arbitrary bounded convex sources are treated separately. *)
Theorem compact_convex_intrinsic_section_comparison (R : realType) m q k (hKQ : (k<=q)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  K !=set0 -> compact K -> is_inner_convex K ->
  exists a : R,
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
        @integral_geometric_gauge R q k hKQ 1
          [set z | K (@euclidean_block_join R m q (y,z))])) a%:E /\
    (a%:E<= @integral_geometric_gauge R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 K)%E.
Proof.
move=> hNonempty hCompact hConvex.
pose N := (m+q)%N.
pose X := inner_metric_space (@euclidean_inner_productP R m).
have [E [G [hEvaluation [hLeft hRight]]]] := @finite_power_evaluation_inverse_exists R N.
pose C := fun y : X => [ffun j : 'I_N.+1 => if (j<=q)%N then
  fine (@integral_geometric_gauge R q (q-j) (leq_subr j q) 1
    [set z | K (@euclidean_block_join R m q (y,z))])*euclidean_unit_ball_volume R j else 0].
pose V : R_n R N.+1 := [ffun j : 'I_N.+1 =>
  fine (@euclidean_lebesgue_measure R N (vector_set_sum K
    ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then 0 else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R N) x<=j.+1%:R])))].
have hQN1 : (q<N.+1)%N := leq_addl m q.
have hIndex : (q-k<N.+1)%N := leq_ltn_trans (leq_subr k q) hQN1.
pose i : 'I_N.+1 := Ordinal hIndex.
pose alpha := euclidean_unit_ball_volume R i.
have hAlpha : 0<alpha := (euclidean_unit_ball_volumeE R i).2.
have hAlphaNonzero : alpha!=0 := lt0r_neq0 hAlpha.
have hI : (i<=q)%N := leq_subr k q.
have hSectionDegree : (q-i)%N=k by change ((q-(q-k))%N=k); rewrite subKn.
have hAmbientDegree : (N-i)%N=(m+k)%N.
  change ((m+q-(q-k))%N=(m+k)%N).
  by rewrite subnBA // addnAC addnK.
pose F := fun y : X => @integral_geometric_gauge R q k hKQ 1
  [set z | K (@euclidean_block_join R m q (y,z))].
have hSectionCast y := @integral_geometric_gauge_index_equality R q (q-i) k (leq_subr i q) hKQ 1
  [set z | K (@euclidean_block_join R m q (y,z))] hSectionDegree.
have hAmbientCast := @integral_geometric_gauge_index_equality R N (N-i) (m+k)
  (leq_subr i N) (leq_add (leqnn m) hKQ) 1 K hAmbientDegree.
have hCoefficient y : C y i=fine (F y)*alpha.
  by rewrite /C ffunE hI hSectionCast.
have hIntegral := (@compact_convex_section_coefficient_integral R m q K E G
  hNonempty hCompact hConvex hEvaluation hLeft) i.
change (is_measure_integral (@euclidean_lebesgue_measure R m)
  (real_total_integrand (fun y => C y i)) (G V i)%:E) in hIntegral.
have hFiniteValue y : F y=(fine (F y))%:E.
  exact: (@compact_convex_intrinsic_finite_part_value R q k hKQ
    [set z | K (@euclidean_block_join R m q (y,z))]
    (@euclidean_block_section_compact R m q K y hCompact)
    (@euclidean_block_section_inner_convex R m q K y hConvex)).
have hActual := @finite_coefficient_integral_unscale R X (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) F (fun y => C y i) alpha (G V i)
  hAlphaNonzero hFiniteValue hCoefficient hIntegral.
have hComparison := (@compact_convex_section_coefficient_comparison R m q K E G
  hNonempty hCompact hConvex hEvaluation hLeft hRight) i.
change (is_true (G V i<=fine (@integral_geometric_gauge R N (N-i) (leq_subr i N) 1 K)*alpha))
  in hComparison.
rewrite hAmbientCast in hComparison.
have hAlphaInverse : 0<alpha^-1 by rewrite invr_gt0.
have hScaledBound := ler_wpM2l (ltW hAlphaInverse) hComparison.
have hCancel z : alpha^-1*(z*alpha)=z by rewrite mulrCA mulVf // mulr1.
rewrite hCancel in hScaledBound.
exists (alpha^-1*G V i); split; first exact hActual.
rewrite (@compact_convex_intrinsic_finite_part_value R N (m+k) (leq_add (leqnn m) hKQ)
  K hCompact hConvex) lee_fin.
exact hScaledBound.
Qed.
