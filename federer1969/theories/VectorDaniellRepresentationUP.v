(** Federer (1969), 2.5.12, printed p. 103, conclusion: the weakly
    measurable dual-valued density represents T by integration of the
    pairing. This specification separates the representation from the
    additional unit-norm conclusion and from any construction of the
    density. Total representatives are used; changing them on a null set
    does not change the integrals. The local erratum has no correction to
    pp. 103–106. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP PartialFunctionBasic MeasureIntegralUP
  MeasurableFunctionUP SummableRealFunctionUP VectorDaniellHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_vector_daniell_density]: direct specification
    of the measurable representing function k in Federer 2.5.12,
    p. 103. Every asserted integral exists and has the stated finite
    value. The norm-one assertion is a further theorem, not a law
    imposed on a candidate representation. *)
Record is_vector_daniell_density (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (Q : set (X -> E)) (T : (X -> E) -> R)
    (k : X -> weak_dual_space hN) : Prop := {
  (** Source for [vector_daniell_density_measurable]: weak
      measurability of k in Federer 2.5.12, p. 103. *)
  vector_daniell_density_measurable :
    is_measure_measurable_function phi (partial_function_total k);
  (** Source for [vector_daniell_density_integral]: the displayed
      representation formula for every w in Q, Federer 2.5.12, p. 103. *)
  vector_daniell_density_integral : forall w, Q w ->
    is_measure_integral phi (real_total_integrand (fun x => val (k x) (w x))) (T w)%:E
}.
