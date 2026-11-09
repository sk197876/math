(** Federer (1969), 3.3.20, p. 307: exact Gross measure of the original critical square. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  PowerCantorPairUP ProjectionMeasure CriticalCantorSquareGrossLower CriticalCantorSquareGrossUpper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_cantor_square_gross]: the exact
    G^1(E)=3/sqrt(5) in 3.3.20, p. 307, with the published
    correction to the supporting first-level projection formulas.
    The actual extremal original projection proves the lower bound;
    arbitrarily fine actual compact original-piece covers prove the upper. *)
Theorem critical_original_cantor_square_gross (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  @gross_measure R 2 1 (euclidean_cantor_product A A)=(3/Num.sqrt (5:R))%:E.
Proof.
move=>hc hPair;apply:le_anti;apply/andP;split.
- exact:critical_original_cantor_square_gross_upper hc hPair.
- exact:critical_original_cantor_square_gross_lower hc hPair.
Qed.
