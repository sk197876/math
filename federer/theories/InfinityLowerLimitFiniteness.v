(** Federer (1969), 2.5.7, p. 98: the bounded limit of candidate densities
    in the q=infinity case. A countable intersection produces a common
    conull set; no sigma-finiteness is needed for this supporting bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureEssentialNormAttainment
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit TotalExtendedLowerLimit TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinity_bounded_total_lower_limit]: the common
    almost-everywhere bound for the limit in Federer 2.5.7, p. 98 Only
    countably many null exceptional sets are combined. *)
Lemma infinity_bounded_total_lower_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (M : R) (f : nat -> X -> R) :
  (forall n, is_measure_measurable_function mu (total_scalar_function (f n))) ->
  (forall n, total_scalar_lp_norm mu +oo (f n) <= M%:E) ->
  measure_almost_everywhere mu
    [set x | total_extended_lower_limit (fun n x => (f n x)%:E) x <= M%:E].
Proof.
move=> hf hb.
have hbound n : measure_almost_everywhere mu [set x | (f n x)%:E <= M%:E].
  have ha := @measure_essential_norm_almost_bound R X R mu hm (fun y : R => `|y|%R)
    (total_scalar_function (f n)) (measurable_function_domain (hf n)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ ha)=> x [y [hy hyb]].
  have he : f n x=y := hy.
  apply: le_trans _ (le_trans hyb (hb n)); rewrite he lee_fin; exact: ler_norm.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => [set x | (f n x)%:E <= M%:E]) (countableP setT) (fun n _ => hbound n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx.
apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> b [K hK].
exact: le_trans (hK K (leqnn K)) (hx K I).
Qed.

(** Source for [infinity_bounded_lower_limit_almost_finite]: almost
    finiteness of the nonnegative limit at q=infinity in Federer 2.5.7, p.
    98 Monotonicity is not needed for this bound. *)
Theorem infinity_bounded_lower_limit_almost_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (M : R) (f : nat -> X -> R) :
  (forall n, is_measure_measurable_function mu (total_scalar_function (f n))) ->
  (forall n x, (0 <= f n x)%R) ->
  (forall n, total_scalar_lp_norm mu +oo (f n) <= M%:E) ->
  measure_almost_everywhere mu
    [set x | total_extended_lower_limit (fun n x => (f n x)%:E) x \is a fin_num].
Proof.
move=> hf hf0 hb.
have ha := @infinity_bounded_total_lower_limit R X mu hm M f hf hb.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ ha)=> x hx.
have h0 : 0 <= total_extended_lower_limit (fun n x => (f n x)%:E) x.
  apply: total_extended_lower_limit_nonnegative=> n y; rewrite lee_fin; exact: hf0.
change (is_true (total_extended_lower_limit (fun n x => (f n x)%:E) x \is a fin_num)).
rewrite (ge0_fin_numE h0); exact: le_lt_trans hx (ltry M).
Qed.
