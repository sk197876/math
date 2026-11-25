(** Federer (1969), 2.6.2(4), pp. 115, 117: inner integrals are used through
    their defining values, and replacing their representatives on a null
    exceptional set preserves the outer integral. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureIntegralGraphEquivalence ParameterizedIntegralUP ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [parameterized_integral_graph_equivalent]:
    supporting graph invariance of the inner integrals in
    Federer 2.6.2(4), p. 115. Equal integrand graphs
    have equal actual integral graphs, retaining exact domains. *)
Lemma parameterized_integral_graph_equivalent (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f g : X -> partial_function Y (extended_real_line R)) :
  (forall x y z, partial_function_graph (f x) y z <-> partial_function_graph (g x) y z) ->
  forall x a, partial_function_graph (parameterized_integral mu f) x a <->
    partial_function_graph (parameterized_integral mu g) x a.
Proof.
move=> he x a; rewrite !parameterized_integral_specification; split=> hi.
- exact (@measure_integral_graph_equivalent R Y mu (f x) (g x) a (he x) hi).
- apply: (@measure_integral_graph_equivalent R Y mu (g x) (f x) a _ hi)=> y z.
  exact: iff_sym (he x y z).
Qed.

(** Source for [parameterized_integral_total_outer_transfer]:
    supporting null-representative step in Federer 2.6.2(4),
    p. 117. A total function agreeing almost everywhere
    with the actual inner integrals has the same outer integral. *)
Lemma parameterized_integral_total_outer_transfer (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (ha : is_measure alpha)
    (f : X -> partial_function Y (extended_real_line R)) (v : X -> extended_real_line R) a :
  measure_almost_everywhere alpha [set x | is_measure_integral beta (f x) (v x)] ->
  is_measure_integral alpha (partial_function_total v) a ->
  is_measure_integral alpha (parameterized_integral beta f) a.
Proof.
move=> hf hv; apply: (@measure_integral_almost_equal R X alpha ha _ _ _ hv).
apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hf)=> x hx.
exists (v x); split=> //; exact: (parameterized_integral_specification beta f x (v x)).2 hx.
Qed.
