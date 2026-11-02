(** Federer (1969), 2.5.14, p. 107, and 2.5.15, pp. 108-109: "we shall see
    in 2.5.15 that K need not be phi measurable. Thus phi may fail to be a
    Radon measure." In the example of 2.5.15 the compact set {xi} is not phi
    measurable, whereas every compact set is measurable for a Radon measure
    by 2.2.5, p. 62. Hence the K(X) regular measure associated with the
    evaluation functional at xi is not a Radon measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP
  CompactSupportFunctionUP RadonMeasureUP RadonBorelRegularity UncountableProductExample.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section NotRadon.
Variable R : realType.
Variable J : choiceType.
Hypothesis hJ : ~ countable (@setT J).

(** Source for [evaluation_regular_measure_not_radon]: Federer 2.5.14,
    p. 107, "Thus phi may fail to be a Radon measure", for the measure
    of 2.5.15, pp. 108-109. Direct formalisation: every measure phi
    which represents lambda(f) = f(xi) on K(X) and is K(X) regular is
    not a Radon measure, because the compact set {xi} is not phi
    measurable (2.5.15) while compact sets are measurable for Radon
    measures (2.2.5, p. 62). *)
Theorem evaluation_regular_measure_not_radon (phi : set (product_space R J) -> \bar R) :
  is_measure phi ->
  is_real_integral_functional phi
    (@compactly_supported_continuous_functions R (product_space R J))
    (@evaluation_functional R J) ->
  is_function_lattice_regular
    (@compactly_supported_continuous_functions R (product_space R J)) phi ->
  ~ is_radon_measure phi.
Proof.
move=> hm hA hr hrad.
apply: (base_point_not_measurable hJ hm hA hr).
exact (radon_compact_measurable hm hrad (@base_point_compact R J)).
Qed.

(** Source for [regular_measure_may_fail_radon]: Federer 2.5.14, p. 107,
    "Thus phi may fail to be a Radon measure", with the example of
    2.5.15, pp. 108-109. Direct formalisation of the existential
    reading: on the compact Hausdorff space X = Y^J the K(X) regular
    measure associated with the monotone Daniell integral lambda exists
    (2.5.3) and is not a Radon measure, while {xi} is a compact set
    which is not phi measurable. *)
Theorem regular_measure_may_fail_radon : exists phi : set (product_space R J) -> \bar R,
  [/\ is_measure phi,
    is_real_integral_functional phi
      (@compactly_supported_continuous_functions R (product_space R J))
      (@evaluation_functional R J),
    is_function_lattice_regular
      (@compactly_supported_continuous_functions R (product_space R J)) phi,
    compact [set @base_point R J] /\ ~ measure_measurable phi [set @base_point R J] &
    ~ is_radon_measure phi].
Proof.
have [phi [hm [hA hr]]] := evaluation_regular_measure_exists R J.
exists phi; split=> //.
- split; first exact: base_point_compact.
  exact (base_point_not_measurable hJ hm hA hr).
- exact (evaluation_regular_measure_not_radon hm hA hr).
Qed.

End NotRadon.
