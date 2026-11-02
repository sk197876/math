(** Federer (1969), 2.5.7, p. 99: norm zero implies almost zero, used for
    uniqueness of the representing density. The norm criteria are in 2.4.12,
    pp. 86–87. These adapters retain the project's total-domain and
    countable-support conventions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureLpZero MeasureEssentialNormAttainment TotalScalarLpUP TotalScalarLpAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_zero_norm_almost_zero]: the zero-norm
    implication used in the uniqueness conclusion of Federer 2.5.7, p. 99
    The finite and infinite exponent cases use their respective norm laws. *)
Lemma total_scalar_lp_zero_norm_almost_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (h : X -> R) :
  total_scalar_lp mu p h -> total_scalar_lp_norm mu p h=0 ->
  measure_almost_everywhere mu [set x | h x=0%R].
Proof.
case: p=> [p| |] hh hz; last by have hbad := hh.1.
- have hp : (1 <= p)%R by move: hh.1; rewrite lee_fin.
  have he := @zero_lp_norm_almost_zero R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p (total_scalar_function h) hp hh.2.1 hz.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x [y [hy hy0]].
  have heh : h x=y := hy.
  have he0 : 0%R=y := hy0.
  change (h x=0%R); by rewrite heh -he0.
- have he := @measure_essential_norm_almost_bound R X R mu hm (fun y : R => `|y|%R)
    (total_scalar_function h) (measurable_function_domain hh.2.1).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x [y [hy hb]].
  change (is_true ((`|y|%R)%:E <= total_scalar_lp_norm mu +oo h)) in hb.
  rewrite hz lee_fin in hb.
  have hy0 : y=0%R by apply/eqP; rewrite -normr_eq0 eq_le hb normr_ge0.
  have heh : h x=y := hy; change (h x=0%R); by rewrite heh hy0.
Qed.

(** Source for [total_scalar_lp_zero_norm_iff]: full zero-norm equivalence
    on the total Lp space used in Federer 2.5.7, pp. 98–99 *)
Lemma total_scalar_lp_zero_norm_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (h : X -> R) :
  total_scalar_lp mu p h ->
  (total_scalar_lp_norm mu p h=0 <-> measure_almost_everywhere mu [set x | h x=0%R]).
Proof.
move=> hh; split.
- exact: (@total_scalar_lp_zero_norm_almost_zero R X mu hm p h hh).
- exact: (@total_scalar_lp_almost_zero_norm R X mu hm p h hh).
Qed.
