(** Ordinary integrability of the original nonclosed convex
    section function in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CoveringFamilyUP EuclideanLinearMaps EuclideanBlockCoordinates VectorSetSum EuclideanLebesgueDimensions EuclideanBallVolume
  IntegralGeometricGauge IntegralGeometricGaugeIndexEquality CompactConvexBlockSections CartesianSectionDiameter
  BoundedConvexVerticalTubeGeometry EuclideanVerticalOpenBallSumSections EuclideanBallVectorSumTube
  BoundedConvexOpenTubePolynomial EuclideanSectionCoefficientIntegral FinitePowerEvaluationExists FinitePowerEvaluationUP
  FiniteCoefficientIntegralUnscale MeasureUP MeasureIntegralUP SummableRealFunctionUP PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_convex_intrinsic_section_integrability]: supporting
    ordinary integral in the original section inequality
    of Federer 3.2.45, p. 279. The original
    bounded convex K need not be closed. Its actual
    open vertical-ball sums are measurable and finite.
    Their original sections are open tubes of the
    original bounded convex fibres. Full Steiner
    polynomials, Fubini and the finite evaluation inverse
    prove the coefficient integrals. Positive alpha
    cancellation gives the original section function's
    finite ordinary integral. Empty and thin fibres
    and both empty coordinate blocks remain. *)
Theorem bounded_convex_intrinsic_section_integrability (R : realType) m q k (hKQ : (k<=q)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  K !=set0 -> is_inner_convex K -> metric_set_bounded K ->
  exists a : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
      @integral_geometric_gauge R q k hKQ 1 [set z | K (@euclidean_block_join R m q (y,z))])) a%:E.
Proof.
move=> hNonempty hConvex hBound.
pose N := (m+q)%N.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Z := inner_metric_space (@euclidean_inner_productP R N).
have [E [G [hEvaluation [hLeft hRight]]]] := @finite_power_evaluation_inverse_exists R N.
pose C := fun y : X => [ffun j : 'I_N.+1 => if (j<=q)%N then
  fine (@integral_geometric_gauge R q (q-j) (leq_subr j q) 1
    [set z | K (@euclidean_block_join R m q (y,z))])*euclidean_unit_ball_volume R j else 0].
pose S := fun j : 'I_N.+1 => vector_set_sum K
  ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then 0 else 1)) @`
    [set x : Z | inner_norm (@euclidean_inner_productP R N) x<j.+1%:R]).
have hGeometry j := @bounded_convex_vertical_open_tube_geometry R N m K j.+1%:R
  hNonempty hConvex hBound (ltr0n R j.+1).
have hMeasurable j : measure_measurable (@euclidean_lebesgue_measure R N) (S j) := (hGeometry j).2.2.1.
have hFinite j : (@euclidean_lebesgue_measure R N (S j)< +oo)%E := (hGeometry j).2.2.2.
have hSections y j : @euclidean_lebesgue_measure R q
    [set z | S j (@euclidean_block_join R m q (y,z))]=(E (C y) j)%:E.
  rewrite /S euclidean_vertical_open_ball_sum_section -euclidean_ball_vector_sum_tube.
  have hPolynomial := @bounded_convex_open_tube_padded_polynomial R q N (leq_addl m q)
    [set z | K (@euclidean_block_join R m q (y,z))] j.+1%:R
    (@euclidean_block_section_inner_convex R m q K y hConvex)
    (@euclidean_bounded_block_section R m q K y hBound) (ltr0n R j.+1).
  rewrite hPolynomial; congr (_%:E); rewrite hEvaluation.
  apply: eq_bigr=> j0 _; by rewrite /C ffunE.
have hIntegrals := @euclidean_section_coefficient_integral R m q E G C S
  hLeft hMeasurable hFinite hSections.
pose V : R_n R N.+1 := [ffun j : 'I_N.+1 => fine (@euclidean_lebesgue_measure R N (S j))].
have hQN1 : (q<N.+1)%N := leq_addl m q.
have hIndex : (q-k<N.+1)%N := leq_ltn_trans (leq_subr k q) hQN1.
pose i : 'I_N.+1 := Ordinal hIndex.
pose alpha := euclidean_unit_ball_volume R i.
have hAlpha : alpha!=0 := lt0r_neq0 (euclidean_unit_ball_volumeE R i).2.
have hI : (i<=q)%N := leq_subr k q.
have hDegree : (q-i)%N=k by change ((q-(q-k))%N=k); rewrite subKn.
pose F := fun y : X => @integral_geometric_gauge R q k hKQ 1
  [set z | K (@euclidean_block_join R m q (y,z))].
have hCast y := @integral_geometric_gauge_index_equality R q (q-i) k (leq_subr i q) hKQ 1
  [set z | K (@euclidean_block_join R m q (y,z))] hDegree.
have hCoefficient y : C y i=fine (F y)*alpha by rewrite /C ffunE hI hCast.
have hFiniteValue y : F y=(fine (F y))%:E.
  exact: (@bounded_convex_intrinsic_finite_part_value R q k hKQ
    [set z | K (@euclidean_block_join R m q (y,z))]
    (@euclidean_block_section_inner_convex R m q K y hConvex)
    (@euclidean_bounded_block_section R m q K y hBound)).
exists (alpha^-1*G V i).
exact: (@finite_coefficient_integral_unscale R X (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) F (fun y => C y i) alpha (G V i)
  hAlpha hFiniteValue hCoefficient (hIntegrals i)).
Qed.
