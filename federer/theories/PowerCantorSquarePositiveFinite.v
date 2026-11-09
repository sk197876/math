(** Federer (1969), 3.3.20, p. 306, and 3.3.21, p. 309:
    the actual original square has positive finite real-degree Hausdorff mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCantorProduct PowerCantorPairUP PowerCantorSquareRealMassBounds
  RealHausdorffMeasure RealHausdorffNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_original_square_positive_finite]:
    the strict positive finite mass assertion
    in 3.3.20, p. 306, and
    3.3.21, p. 309. The exact
    original lower and upper bounds, with actual
    Euler Gamma normalization, prove both strict
    inequalities for every original schedule and
    every real 0<m<1. No mass assumption
    or replacement Cantor carrier is supplied. *)
Theorem power_cantor_original_square_positive_finite (R:realType) (c m:R)
    (hDegree:(0<=2 * m)%R) (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  0<c ->0<m ->m<1 ->is_power_cantor_pair c m n A f ->
  (0<@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
    (2 * m) hDegree (euclidean_cantor_product A A)< +oo)%E.
Proof.
move=>hc hm hm1 hPair.
have [hLower hUpper]:=@power_cantor_square_real_mass_bounds R c m hDegree n A f hc hm hm1 hPair.
have hPositive:(0<(real_hausdorff_normalisation hDegree)%:E)%E.
  rewrite lte_fin;exact:real_hausdorff_normalisation_positive.
apply/andP;split.
- exact:lt_le_trans hPositive hLower.
- exact:le_lt_trans hUpper (ltry _).
Qed.
