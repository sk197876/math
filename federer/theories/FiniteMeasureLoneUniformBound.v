(** Federer (1969), 4.1.7, p. 358:
    a uniform error on a finite
    variation measure bounds the original L1
    distance. This is a direct adapter
    to 2.4.4(5), p. 82, and
    the L1 distance integral already used
    in 2.5.12, pp. 104–105. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasurableNormedFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralComparison SummableRealFunctionUP MeasureLpConvergence
  SeparableVectorLone FiniteMeasureBoundedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_measure_lone_almost_uniform_bound]:
    the original L1 distance is at
    most the uniform norm error times
    the finite total measure, supporting
    the class-one boundary limit in Federer
    4.1.7, p. 358. The norm
    is the original finite-p norm, with
    its actual integral graph. *)
Theorem finite_measure_lone_almost_uniform_bound (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) mass bound
    (f g:X->real_norm_metric_space hNY):
  mu setT=mass%:E->
  is_measurable_normed_function mu (partial_function_total f)->
  is_measurable_normed_function mu (partial_function_total g)->
  measure_almost_everywhere mu [set x|NY (f x-g x)<=bound]->
  (measure_lp_distance mu NY 1 (partial_function_total f) (partial_function_total g)<=
    (bound*mass)%:E)%E.
Proof.
move=>hMass hf hg hBound.
have hNorm:=@total_vector_lone_distance_integral R X Y NY hNY mu hm f g hf hg.
have hConstant:=@finite_measure_constant_integral R X mu hm mass bound hMass.
apply:(@measure_integral_monotone R X mu hm _ _ _ _ hNorm hConstant).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hBound)=>x hx.
exists (NY (f x-g x))%:E,bound%:E;split.
- by apply/real_total_integrand_graph.
- split;first by [].
  rewrite lee_fin;exact:hx.
Qed.

(** Source for [finite_measure_lone_uniform_bound]:
    the everywhere uniform bound is a
    special case of the original almost
    comparison, supporting Federer 4.1.7,
    p. 358. *)
Theorem finite_measure_lone_uniform_bound (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) mass bound
    (f g:X->real_norm_metric_space hNY):
  mu setT=mass%:E->
  is_measurable_normed_function mu (partial_function_total f)->
  is_measurable_normed_function mu (partial_function_total g)->
  (forall x,NY (f x-g x)<=bound)->
  (measure_lp_distance mu NY 1 (partial_function_total f) (partial_function_total g)<=
    (bound*mass)%:E)%E.
Proof.
move=>hMass hf hg hBound.
apply:(@finite_measure_lone_almost_uniform_bound R X Y NY hNY mu hm mass bound f g hMass hf hg).
apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _;exact:hBound.
Qed.
