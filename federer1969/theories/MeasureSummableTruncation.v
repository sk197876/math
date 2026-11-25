(** Federer (1969), 2.4.11, proof p. 86: increasing convergence gives
    integral gn tending to integral |f|, which is finite. The supporting
    statement is given for any nonnegative summable function. Source
    editions: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP PartialUpperTruncation
  MeasureUP MeasureAlmostUP MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasurableUpperTruncation MeasureTruncationOrder MeasureNonnegativeIntegral MeasureIntegralComparison
  PartialTruncationLowerLimit MeasureIncreasingConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_nonnegative_truncation_integrals]: supporting
    finite integrals of gn in Federer 2.4.11,
    proof p. 86, bounded by the original finite integral. *)
Lemma measure_nonnegative_truncation_integrals (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (b : R) :
  is_measure_integral mu f b%:E -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  forall n, let g := partial_upper_truncation f (n.+1)%:R%:E in
    is_measure_integral mu g (measure_lower_integral mu g) /\
    0 <= measure_lower_integral mu g /\ measure_lower_integral mu g <= b%:E /\
    measure_lower_integral mu g \is a fin_num.
Proof.
move=> hf hp n g.
have hcap : (0 : \bar R) <= (n.+1)%:R%:E by rewrite lee_fin ler0n.
have hgm := @measurable_upper_truncation R X mu hm f (n.+1)%:R%:E hf.1.
have hgp := @measure_upper_truncation_nonnegative R X mu hm f _ hcap hp.
have [hi hpos] := @nonnegative_measurable_function_integral R X mu hm g hgm hgp.
have hbound := @measure_integral_monotone R X mu hm g f _ b%:E hi hf
  (@measure_upper_truncation_below R X mu hm f _ (measurable_function_domain hf.1)).
split=> //; split=> //; split=> //.
rewrite (ge0_fin_numE hpos); exact: le_lt_trans hbound (ltry b).
Qed.

(** Source for [measure_summable_truncation_limit]: direct
    application of 2.4.7 in the proof of Federer
    2.4.11, p. 86. The integral limit is finite. *)
Lemma measure_summable_truncation_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (b : R) :
  is_measure_integral mu f b%:E -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  extended_increases_to (fun n => measure_lower_integral mu (partial_upper_truncation f (n.+1)%:R%:E)) b%:E.
Proof.
move=> hf hp; apply: (@measure_increasing_integral_values R X mu hm
  (fun n => partial_upper_truncation f (n.+1)%:R%:E) f _ b%:E
  (partial_upper_truncation_lower_limit f) _ _ _ hf).
- move=> n; apply: (@measure_upper_truncation_nonnegative R X mu hm f _ _ hp); by rewrite lee_fin ler0n.
- move=> n; apply: (@measure_upper_truncation_increasing R X mu hm f _ _ _ (measurable_function_domain hf.1)).
  by rewrite lee_fin ler_nat leqnSn.
- move=> n; exact (@measure_nonnegative_truncation_integrals R X mu hm f b hf hp n).1.
Qed.
