(** Federer (1969), 2.4.12, pp. 87–88: the continuous dual and the defining
    dual evaluations of the vector-valued integral. The construction and
    existence of the integral are separate from these abstract
    characterisation and uniqueness laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition
  ExtendedRealOrderTopology MeasureIntegralUP MeasureIntegralUniqueness MeasureLpMembershipUP
  ContinuousRealFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_functional_evaluation]: exact partial
    composite alpha o f in the defining display of Federer
    2.4.12, p. 87. Scalar values are included into
    the extended-real integral theory without extending the domain. *)
Definition partial_functional_evaluation (R : realType) (X : Type) (V : lmodType R)
    (f : partial_function X V) (a : {linear V -> R^o}) : partial_function X (extended_real_line R) :=
  partial_function_postcompose f (fun y => (a y)%:E).

(** Source for [is_measure_vector_integral]: the abstract dual specification
    of integral f in Federer 2.4.12, p. 87 The stated L1 domain is part of
    the specification; no existence axiom is assumed. *)
Definition is_measure_vector_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) (y : V) :=
  is_measure_lp_function mu 1%R f /\
  forall a : {linear V -> R^o}, is_continuous_real_functional hN a ->
    is_measure_integral mu (partial_functional_evaluation f a) (a y)%:E.

(** Source for [measure_vector_integral_unique]: uniqueness implicit in the
    definition of Federer 2.4.12, pp. 87–88, proved. *)
Theorem measure_vector_integral_unique (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) (y z : V) :
  is_measure_vector_integral mu f y -> is_measure_vector_integral mu f z -> y=z.
Proof.
move=> [_ hy] [_ hz]; apply: (@continuous_real_functionals_separate R V N hN y z)=> a ha.
have he := measure_integral_unique (hy a ha) (hz a ha).
by injection he.
Qed.
