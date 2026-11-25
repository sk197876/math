(** Individual section-coefficient comparison for Federer
    (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps VectorSetSum EuclideanLebesgueDimensions EuclideanBallVolume IntegralGeometricGauge
  FinitePowerEvaluationUP FinitePowerEvaluationOrderBound ConvexCompressedSteinerCoefficient
  ConvexCompressedAscendingPolynomial EuclideanPrefixBallSumVolumeLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_section_coefficient_comparison]: supporting
    comparison of each original section and ambient tube
    coefficient in Federer 3.2.45, pp. 279–280.
    The separate coordinate-stretch estimates bound every
    determinant-normalized coefficient. Actual compressed
    ball-sum volumes converge at the finitely many
    positive evaluation nodes. The proved finite inverse
    then identifies each individual limit and retains
    its upper bound. This supplies the specific
    coefficient comparison needed here without assuming
    it as mixed-volume monotonicity or inferring it
    from a pointwise polynomial order. Original thin
    bodies and all natural coordinate blocks remain. *)
Theorem compact_convex_section_coefficient_comparison (R : realType) m q
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q))))
    (E G : {linear R_n R (m+q).+1 -> R_n R (m+q).+1}) :
  K !=set0 -> compact K -> is_inner_convex K ->
  is_finite_power_evaluation E -> cancel E G -> cancel G E ->
  let V : R_n R (m+q).+1 := [ffun j : 'I_(m+q).+1 =>
    fine (@euclidean_lebesgue_measure R (m+q) (vector_set_sum K
      ((@euclidean_diagonal_map R (m+q) (fun l => if (l<m)%N then 0 else 1)) @`
        [set x | inner_norm (@euclidean_inner_productP R (m+q)) x<=j.+1%:R])))] in
  forall i : 'I_(m+q).+1,
    G V i<=fine (@integral_geometric_gauge R (m+q) (m+q-i) (leq_subr i (m+q)) 1 K)*
      euclidean_unit_ball_volume R i.
Proof.
move=> hNonempty hCompact hConvex hEvaluation hLeft hRight V.
pose N := (m+q)%N.
pose Z := inner_metric_space (@euclidean_inner_productP R N).
pose h := fun s : nat => (s.+1%:R : R)^-1.
pose S := fun (a r : R) => vector_set_sum K
  ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then a else 1)) @`
    [set x : Z | inner_norm (@euclidean_inner_productP R N) x<=r]).
pose c := fun s : nat => [ffun i : 'I_N.+1 =>
  ((h s)^+m*fine (@integral_geometric_gauge R N (N-i) (leq_subr i N) 1
    ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then (h s)^-1 else 1)) @` K)))*
    euclidean_unit_ball_volume R i].
pose b : R_n R N.+1 := [ffun i : 'I_N.+1 =>
  fine (@integral_geometric_gauge R N (N-i) (leq_subr i N) 1 K)*euclidean_unit_ball_volume R i].
have hPositive s : 0<h s by rewrite /h invr_gt0 ltr0n.
have hAtMostOne s : h s<=1 by rewrite /h invf_le1 ?ltr0n // ler1n.
have hValues s j : E (c s) j=fine (@euclidean_lebesgue_measure R N (S (h s) j.+1%:R)).
  have hPolynomial := @convex_compressed_ball_ascending_polynomial R m q K (h s) j.+1%:R
    hNonempty hCompact hConvex (hPositive s) (ltr0n R j.+1).
  rewrite hEvaluation /S hPolynomial.
  change ((\sum_(i : 'I_N.+1) c s i*(j.+1%:R)^+i)=
    (\sum_(i : 'I_N.+1)
      (((h s)^+m*fine (@integral_geometric_gauge R N (N-i) (leq_subr i N) 1
        ((@euclidean_diagonal_map R N (fun l => if (l<m)%N then (h s)^-1 else 1)) @` K)))*
        euclidean_unit_ball_volume R i)*(j.+1%:R)^+i)).
  apply: eq_bigr=> i _; by rewrite /c ffunE.
have hLimits j : extended_order_limit (fun s => (E (c s) j)%:E) (E (G V) j)%:E.
  have hFunction : (fun s => (E (c s) j)%:E)=
      (fun s => (fine (@euclidean_lebesgue_measure R N (S (h s) j.+1%:R)))%:E).
    by apply: funext=> s; rewrite hValues.
  rewrite hFunction hRight /V ffunE.
  exact: (@euclidean_prefix_ball_sum_volume_sequence_limit R N m K j.+1%:R
    hNonempty hCompact hConvex (ltW (ltr0n R j.+1))).
have hBounds s i : c s i<=b i.
  rewrite /c /b !ffunE.
  have hCoefficient := @convex_compressed_steiner_coefficient_bound R N (N-i) (leq_subr i N)
    m (leq_addr q m) K (h s) hNonempty hCompact hConvex (hPositive s) (hAtMostOne s).
  have hScaled := ler_wpM2r (ltW (euclidean_unit_ball_volumeE R i).2) hCoefficient.
  exact hScaled.
have hBound := @finite_power_evaluation_coefficient_upper_bound R N E G c (G V) b
  hLeft hLimits hBounds.
move=> i; have hI := hBound i; by rewrite /b ffunE in hI.
Qed.
