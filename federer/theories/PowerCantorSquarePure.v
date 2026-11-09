(** Federer (1969), 3.3.20, p. 306:
    actual original Cantor-square purity and the finite infinity-measure obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCantorProduct PowerCantorPairUP PowerCantorPair NullFactorSquarePure
  RectifiableSetUP HausdorffMeasure RealHausdorffMeasure IntegralGeometricMeasure
  PureHigherRealHausdorffDegree PureFiniteInfinityMassZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_original_square_pure_length]:
    the pure (H1,1) conclusion in 3.3.20,
    p. 306. Actual original factor compactness
    and Lebesgue nullity discharge the coordinate
    proof. The supporting result holds for every
    original schedule and 0<m<1, strengthening the
    printed fixed-binary m>=1/2 case. *)
Theorem power_cantor_original_square_pure_length (R:realType) (c m:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  0<c ->0<m ->m<1 ->is_power_cantor_pair c m n A f ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 2)) 1) 1 (euclidean_cantor_product A A).
Proof.
move=>hc hm hm1 hPair.
have [hCompact [_ [_ [_ [_ [_ [_ [hNull _]]]]]]]]:=
  @power_cantor_pair_properties R c m n A f hc hm hm1 hPair.
exact:compact_null_factor_square_pure_length hCompact hNull.
Qed.

(** Source for [power_cantor_original_square_pure_consequences]:
    both remaining purity consequences on p. 306
    of 3.3.20: actual pure (H^(2m),1)
    unrectifiability and absence of any original
    subset of finite positive I_infinity^1 mass.
    Every real m>=1/2 below one remains,
    with actual Gamma-normalized Hausdorff measure.
    No source or subset measurability premise is added. *)
Theorem power_cantor_original_square_pure_consequences (R:realType) (c m:R)
    (hDegree:(0<=2 * m)%R) (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  0<c ->1/2<=m ->m<1 ->is_power_cantor_pair c m n A f ->
  is_purely_measure_m_unrectifiable (@real_hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 2)) (2 * m) hDegree) 1 (euclidean_cantor_product A A) /\
  forall F,F `<=` euclidean_cantor_product A A ->
    (@integral_geometric_measure R 2 1 (erefl true) +oo F< +oo)%E ->
    @integral_geometric_measure R 2 1 (erefl true) +oo F=0%E.
Proof.
move=>hc hmHalf hm1 hPair.
have hm:0<m by lra.
have hPure:=power_cantor_original_square_pure_length hc hm hm1 hPair.
split.
- apply:(@pure_higher_real_hausdorff_degree R 2 (2 * m) hDegree _ _ hPure);lra.
- move=>F hFE hFinite;exact:(@pure_original_finite_infinity_mass_zero R 2 1 (erefl true)
    (euclidean_cantor_product A A) F hPure hFE hFinite).
Qed.
