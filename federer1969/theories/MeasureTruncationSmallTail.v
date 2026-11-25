(** Federer (1969), 2.4.11, proof p. 86, first paragraph: a positive
    truncation level can be chosen so that integral(|f|-gn) is less than
    epsilon/2. we retain Federer's strict bound. Source context:
    PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic PartialUpperTruncation
  MeasureUP MeasureAlmostUP PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralDifference MeasureSummableTruncation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_summable_truncation_small_tail]: the
    small-tail choice in Federer 2.4.11, proof p. 86,
    for an arbitrary positive tolerance. The level n+1
    is automatically positive. *)
Lemma measure_summable_truncation_small_tail (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (b e : R) :
  is_measure_integral mu f b%:E -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < e)%R ->
  exists n (t : R), (0 <= t < e)%R /\
    is_measure_integral mu (partial_extended_function_subtract f (partial_upper_truncation f (n.+1)%:R%:E)) t%:E.
Proof.
move=> hf hp he; have hlim := @measure_summable_truncation_limit R X mu hm f b hf hp.
have hbe : (b-e)%:E < b%:E by rewrite lte_fin ltrBlDr ltrDl.
have [n hn] := hlim.2.1 _ hbe.
have [hi [hpos [hbound hfin]]] := @measure_nonnegative_truncation_integrals R X mu hm f b hf hp n.
pose a := fine (measure_lower_integral mu (partial_upper_truncation f (n.+1)%:R%:E)).
have hai : is_measure_integral mu (partial_upper_truncation f (n.+1)%:R%:E) a%:E by rewrite /a fineK.
have hab : (a <= b)%R by move: hbound; rewrite -(fineK hfin) lee_fin.
have hsmall : (b-a < e)%R.
  have h := hn n (leqnn n); rewrite -(fineK hfin) lte_fin in h.
  rewrite ltrBlDr addrC -ltrBlDr; exact h.
exists n,(b-a)%R; split.
- by rewrite subr_ge0 hab hsmall.
- exact (@measure_integral_finite_difference R X mu hm f _ b a hf hai).
Qed.
