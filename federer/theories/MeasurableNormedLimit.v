(** Federer (1969), 2.3.9, pp. 79–80: the almost-everywhere limit belongs to
    A(mu,Y), as needed for completeness in 2.3.10, p. 80. Measurability is
    2.3.2(6), pp. 73–74; closedness gives essential separability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePartialLimits
  MeasurableNormedFunctionUP EssentialSeparableEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_almost_limit]: supporting closure of
    A(mu,Y) under almost-everywhere limits for Federer 2.3.9, pp. 79–80
    Completeness is not needed when the limit is already supplied. *)
Theorem measurable_normed_almost_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  is_measurable_normed_function mu g.
Proof.
move=> hf hl; split.
- exact (@measurable_partial_functions_almost_limit R X [the metricType R of real_norm_metric_space hN]
    mu hm f g (fun n => (hf n).1) hl).
have [Z [hc [hd hZ]]] := @essential_separable_sequence_envelope R X V N hN mu hm f (fun n => (hf n).2).
exists Z; split=> //.
pose E := \bigcup_n partial_function_preimage (f n) [set y | ~ Z y].
have hE : mu E = 0.
  apply: (@measure_null_countable_union R X nat mu hm setT _ (countableP _))=> n _; exact: hZ.
have hnull : mu ((~` partial_function_limit_locus f g) `|` E) = 0.
  exact: measure_null_union hl hE.
apply: (@measure_null_subset R X mu hm _ _ _ hnull).
move=> x [y [hgy hnZ]]; case: (pselect (partial_function_limit_locus f g x))=> hx.
2: by left.
right; apply: contrapT=> hnE.
have [u [z [hu [hgz hlim]]]] := hx.
have he : y=z := partial_function_single_valued hgy hgz.
have hseq : forall n, Z (u n).
  move=> n; apply: contrapT=> hn; apply: hnE; exists n=> //.
  exists (u n); by split.
have hevent : \forall n \near \oo, Z (u n).
  exists 0%N=> // n hn; exact: hseq.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have hz : Z z := @closed_cvg nat [the topologicalType of real_norm_metric_space hN] \oo PF0 u (fun y : real_norm_metric_space hN => Z y) hc hevent z hlim.
apply: hnZ; rewrite he; exact hz.
Qed.
