(** Federer (1969), 2.5.7, p. 98: preserve the uniform norm bound when
    passing to the candidate limit. The inequality is Federer 2.4.12, p. 87.
    These total-domain adapters retain infinity among the exponents and
    among the norm values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP MeasureUP
  MeasureAlmostUP MeasurableFunctionUP ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit
  MeasureLpNormLowerLimit MeasureEssentialNormLowerLimit TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_norm_lower_semicontinuous]: complete
    lower-semicontinuity inequality 2.4.12, p. 87, on the corrected total
    domain of Federer 2.5.7, p. 98 *)
Theorem total_scalar_lp_norm_lower_semicontinuous (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : \bar R)
    (f : nat -> X -> R) (g : X -> R) :
  1 <= p ->
  (forall n, is_measure_measurable_function mu (total_scalar_function (f n))) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => total_scalar_function (f n)) (total_scalar_function g)) ->
  total_scalar_lp_norm mu p g <= extended_lower_limit (fun n => total_scalar_lp_norm mu p (f n)).
Proof.
case: p=> [p| |] hp hf hg hl; last by [].
- have hp' : (1 <= p)%R by move: hp; rewrite lee_fin.
  exact: (@measure_lp_norm_lower_semicontinuous R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p _ _ hp' hf hg hl).
- exact: (@measure_essential_norm_lower_semicontinuous R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm _ _ hl).
Qed.

(** Source for [total_scalar_lp_limit_uniform_bound]: preservation of the
    common Lq bound M in Federer 2.5.7, p. 98 This supporting consequence
    applies to arbitrary almost-everywhere convergent sequences. *)
Lemma total_scalar_lp_limit_uniform_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : \bar R)
    (f : nat -> X -> R) (g : X -> R) (M : R) :
  1 <= p ->
  (forall n, is_measure_measurable_function mu (total_scalar_function (f n))) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => total_scalar_function (f n)) (total_scalar_function g)) ->
  (forall n, total_scalar_lp_norm mu p (f n) <= M%:E) ->
  total_scalar_lp_norm mu p g <= M%:E.
Proof.
move=> hp hf hg hl hb.
apply: le_trans (@total_scalar_lp_norm_lower_semicontinuous R X mu hm p f g hp hf hg hl) _.
apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> b [K hK].
exact: le_trans (hK K (leqnn K)) (hb K).
Qed.
