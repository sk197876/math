(** Federer (1969), 2.5.7, p. 99: a null-supported separating function has
    zero norm. This uses the almost-equality invariance in 2.4.12, pp.
    86–87. These total-domain consequences retain infinity among the
    exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureLpNormAlmostEquality MeasureEssentialNormComparison
  TotalScalarLpUP TotalScalarLpNormLaws TotalScalarLpClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_norm_almost_equal]: almost- equality
    invariance from 2.4.12, pp. 86–87, on the corrected total domain of
    Federer 2.5.7, p. 98 *)
Lemma total_scalar_lp_norm_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p g ->
  measure_almost_everywhere mu [set x | f x=g x] ->
  total_scalar_lp_norm mu p f=total_scalar_lp_norm mu p g.
Proof.
move=> hf hg he.
have heq : measure_almost_equal mu (total_scalar_function f) (total_scalar_function g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  exists (f x); split=> //; by rewrite hx.
case: p hf hg=> [p| |] hf hg; last by have hh := hf.1.
- have hp : (1 <= p)%R by move: hf.1; rewrite lee_fin.
  exact: (@measure_lp_norm_almost_equal R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p _ _ hp hf.2.1 hg.2.1 heq).
- exact: (@measure_essential_norm_almost_equal R X R mu hm (fun y : R => `|y|%R) _ _ heq).
Qed.

(** Source for [total_scalar_lp_almost_zero_norm]: the implication h=0
    almost everywhere => phi_(p)(h)=0 in Federer 2.5.7, p. 99 Full Lp
    membership of h remains explicit. *)
Lemma total_scalar_lp_almost_zero_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (h : X -> R) :
  total_scalar_lp mu p h -> measure_almost_everywhere mu [set x | h x=0%R] ->
  total_scalar_lp_norm mu p h=0.
Proof.
move=> hh he.
have hz := @total_scalar_lp_zero R X mu hm p hh.1.
rewrite (@total_scalar_lp_norm_almost_equal R X mu hm p h (fun _ => 0%R) hh hz he).
exact: (@total_scalar_lp_norm_zero R X mu hm p hh.1).
Qed.
