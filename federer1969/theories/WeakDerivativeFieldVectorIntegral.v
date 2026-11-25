(** Federer (1969), 2.9.22, pp. 167–168: the vector integral of v over [a,b]
    is g(b)-g(a), by evaluation against every element of Y*. This proof uses
    only the abstract vector-integral specification from 2.4.12, pp. 87–88. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  ContinuousRealFunctional ContinuousDualUP MeasureUP MeasureRestriction MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureVectorIntegralUP LebesgueScalarMeasure
  ReflexiveLipschitzFieldUP BoundedRestrictedVectorIntegrability WeakDerivativeFieldScalarIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_functional_evaluation_graph]: supporting
    exact scalar-evaluation graph in the vector-integral display
    of Federer 2.9.22, pp. 167–168, by the definition
    in 2.4.12, p. 87. Total input maps give precisely
    the finite evaluation alpha(v(x)), without a domain extension. *)
Lemma total_functional_evaluation_graph (R : realType) (X : Type) (E : lmodType R)
    (v : X -> E) (alpha : {linear E -> R^o}) x y :
  partial_function_graph (partial_functional_evaluation (partial_function_total v) alpha) x y <->
  (alpha (v x))%:E=y.
Proof.
split.
- by move=> [z [hz he]]; rewrite -(hz : v x=z) in he.
- move=> he; exists (v x); by split.
Qed.

(** Source for [weak_derivative_field_vector_integral]: direct
    vector identity integral_[a,b] v = g(b)-g(a) in Federer
    2.9.22, p. 168, first display, following the dual
    calculation on p. 167. Full L1 membership is proved
    from boundedness and separability; every continuous linear
    functional is then represented by the supplied abstract dual.
    No stronger derivative existence statement is assumed. *)
Theorem weak_derivative_field_vector_integral (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g v : R -> E) (L a b : R)
    (C : set (real_norm_metric_space hN)) :
  countable C -> dense C -> 0<=L ->
  (forall t u, N (g t-g u)<=L * `|t-u|) ->
  is_bounded_weak_derivative_field hN ed (@lebesgue_scalar_measure R) g v L -> a<b ->
  is_measure_vector_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total (v : real_line_metric R -> real_norm_metric_space hN)) (g b-g a).
Proof.
move=> hCc hCd hL hg hv hab.
have hm := lebesgue_scalar_is_measure R.
have hmass := lebesgue_scalar_segment (ltW hab).
have hf := @bounded_restricted_vector_lone R (real_line_metric R) E N hN C
  (@lebesgue_scalar_measure R) hm `[a,b] (b-a) L v hCc hCd hmass
  (bounded_weak_field_measurable hv) (bounded_weak_field_bound hv).
split=> // alpha halpha.
have [d hd] := continuous_dual_surjective hD (a:=hom_of_linear alpha) halpha.
have hi := @weak_derivative_field_scalar_integral R E D N hN ed DN hD g v L a b
  hL hg hv hab d.
rewrite hd !hom_of_linearE in hi.
apply: (@measure_integral_graph_equivalent R (real_line_metric R)
  (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
  _ _ _ _ hi)=> x y.
by rewrite total_functional_evaluation_graph.
Qed.
