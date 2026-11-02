(** Federer (1969), 2.5.9, p. 100: identify total L1 functions with summable
    total real functions, as required for the positive-density assertion of
    2.5.3, p. 94. The norm formula is 2.4.12, p. 86. These are compatibility
    lemmas between existing abstract definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasurableFunctionUP MeasurableTotalBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureLoneNormIntegralGeneral MeasureLpCountableMeasurability MeasureExponentDomain
  SummableRealFunctionUP SummableRealArithmetic SummableRealNormed
  TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lone_norm_from_absolute_integral]: the norm equals the
    integral of |f|, Federer 2.4.12, p. 86, supporting 2.5.9, p. 100 *)
Lemma total_lone_norm_from_absolute_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (a : R) :
  is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x|%R)) a%:E ->
  total_scalar_lp_norm mu 1 f=a%:E.
Proof.
move=> hf hi.
have hn := @measurable_lone_norm_integral R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu hm (total_scalar_function f) hf.
have hni : is_measure_integral mu (real_total_integrand (fun x => `|f x|%R))
    (total_scalar_lp_norm mu 1 f).
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hn)=> x z.
  rewrite real_total_integrand_graph; split.
  - move=> [y [hy he]]; by rewrite -(hy : f x=y) real_power_one_exponent ?normr_ge0 in he.
  - move=> he; exists (f x); split=> //; by rewrite real_power_one_exponent ?normr_ge0.
exact: measure_integral_unique hni hi.
Qed.

(** Source for [summable_real_total_lone]: the identification used in
    Federer 2.5.9, p. 100, before the density extension Countable
    measurability of the support is proved from finite L1 norm. *)
Lemma summable_real_total_lone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  summable_real_functions mu f -> total_scalar_lp mu 1 f.
Proof.
move=> hs.
have hf := (@summable_real_function_in_normed_collection R X mu hm f hs).1.
have [a ha] := @summable_real_absolute R X mu hm f hs.
have he := @total_lone_norm_from_absolute_integral R X mu hm f a hf ha.
have hfin : total_scalar_lp_norm mu 1 f < +oo by rewrite he ltry.
split; first exact: lexx.
split=> //; split=> //.
exact: (@finite_lp_norm_countably_measurable R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu hm 1%R (total_scalar_function f) (lexx _) hf hfin).
Qed.

(** Source for [total_lone_summable_real]: reverse identification supporting
    Federer 2.5.9, p. 100 The integral of f is obtained using the already
    proved bounded-factor pairing with the constant one. *)
Lemma total_lone_summable_real (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  total_scalar_lp mu 1 f -> summable_real_functions mu f.
Proof.
move=> hf.
have h1 := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 1%R.
have ha : measure_almost_everywhere mu [set x : X | (`|(1%R : R)| <= 1)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; change (is_true ((`|(1%R : R)| <= 1)%R)); by rewrite normr1 lexx.
have [a [hi hb]] := @total_scalar_pairing_bounded_factor R X mu hm f (fun _ => 1%R) 1%R hf h1 (ler01) ha.
have he : (fun x => (f x*1)%R)=f by apply: funext=> x; rewrite mulr1.
exists a; by rewrite he in hi.
Qed.
