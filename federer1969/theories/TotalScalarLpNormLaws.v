(** Federer (1969), 2.5.7, p. 98: the seminorm on total scalar Lp functions.
    Its three laws are those of 2.4.12, pp. 86–87; the erratum p. 2, book p.
    98 line 10, requires the total-domain restriction. These consequences
    use the existing sealed finite and essential norms. *)
From mathcomp Require Import all_boot all_order all_algebra functions boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasurableRealNormed MeasurableTotalBasic ExtendedSeminormUP MeasureExponentDomain
  MeasureLpNorm MeasureLpNormTotal MeasureEssentialNorm MeasureEssentialNormTotal TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_norm_nonnegative]: nonnegativity in Federer
    2.4.12, p. 86, restricted to the space in 2.5.7, p. 98 *)
Lemma total_scalar_lp_norm_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  1 <= p -> is_measure_measurable_function mu (total_scalar_function f) ->
  0 <= total_scalar_lp_norm mu p f.
Proof.
case: p=> [p| |] hp hf; last by [].
- exact: (@measure_lp_norm_nonnegative R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu p (total_scalar_function f) hm hp hf).
- exact: measure_essential_norm_nonnegative.
Qed.

(** Source for [total_scalar_lp_norm_scale]: absolute homogeneity used to
    normalize the closed ball in Federer 2.5.7, p. 98 Zero scalars are
    included. *)
Lemma total_scalar_lp_norm_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (c : R) (f : X -> R) :
  1 <= p -> is_measure_measurable_function mu (total_scalar_function f) ->
  total_scalar_lp_norm mu p (fun x => (c*f x)%R)=`|c|%:E*total_scalar_lp_norm mu p f.
Proof.
case: p=> [p| |] hp hf; last by [].
- exact: (@total_lp_norm_scale R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p hp c f
    (@measurable_real_function_in_normed_space R X mu hm _ hf)).
- have hh := (@extended_seminorm_scale R (GRing.Lmodule.clone R (X -> R^o) _) _
    (@total_measure_essential_norm_seminorm R X R^o (fun y : R => `|y|%R)
      (scalar_absolute_value_norm R).1 mu hm) c f).
  exact hh.
Qed.

(** Source for [total_scalar_lp_norm_triangle]: the seminorm triangle law in
    Federer 2.4.12, p. 87, on the total-domain space in 2.5.7, p. 98 *)
Lemma total_scalar_lp_norm_triangle (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  1 <= p -> is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  total_scalar_lp_norm mu p (fun x => (f x+g x)%R) <=
    total_scalar_lp_norm mu p f+total_scalar_lp_norm mu p g.
Proof.
case: p=> [p| |] hp hf hg; last by [].
- exact: (@total_lp_norm_triangle R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p hp f g
    (@measurable_real_function_in_normed_space R X mu hm _ hf)
    (@measurable_real_function_in_normed_space R X mu hm _ hg)).
- have hh := (@extended_seminorm_triangle R (GRing.Lmodule.clone R (X -> R^o) _) _
    (@total_measure_essential_norm_seminorm R X R^o (fun y : R => `|y|%R)
      (scalar_absolute_value_norm R).1 mu hm) f g).
  exact hh.
Qed.

(** Source for [total_scalar_lp_norm_zero]: zero is in the corrected closed
    ball of Federer 2.5.7, p. 98 No finite total mass is needed. *)
Lemma total_scalar_lp_norm_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p :
  1 <= p -> total_scalar_lp_norm mu p (fun _ : X => 0%R)=0.
Proof.
move=> hp.
have hz := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R.
have hh := @total_scalar_lp_norm_scale R X mu hm p 0%R (fun _ => 0%R) hp hz.
have he : (fun _ : X => (0*0)%R)=(fun _ => (0%R : R)) by apply: funext=> x; rewrite mul0r.
by rewrite he normr0 mul0e in hh.
Qed.
