(** Federer (1969), 2.9.1, pp. 152–153: the standing metric-measure context
    for derivates. The definitions below retain Federer's class M. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP CoveringFamilyUP CoveringRelationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_derivation_measure]: direct specification of M in Federer
    2.9.1, p. 152: Borel regular measures over the metric space, finite on
    all bounded sets. *)
Record is_derivation_measure (R : realType) (X : metricType R)
    (psi : set X -> \bar R) : Prop := {
  (** Source for [derivation_measure_law]: measure law in
      the definition of M, Federer 2.9.1, p. 152. *)
  derivation_measure_law : is_measure psi;
  (** Source for [derivation_measure_borel_regular]: Borel
      regularity in M, Federer 2.9.1, p. 152. *)
  derivation_measure_borel_regular : is_borel_regular_measure psi;
  (** Source for [derivation_measure_bounded_finite]: bounded-set finiteness
    in M, Federer 2.9.1, p. 152. *)
  derivation_measure_bounded_finite : forall A, metric_set_bounded A -> psi A < +oo
}.

(** Source for [is_measure_derivation_context]: the standing
    pair phi,V in Federer 2.9.1, p. 152:
    phi belongs to M and V is a phi Vitali relation
    as defined in 2.8.16, p. 151. *)
Record is_measure_derivation_context (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) : Prop := {
  (** Source for [derivation_context_measure]: the condition
      phi in M in Federer 2.9.1, p. 152. *)
  derivation_context_measure : is_derivation_measure phi;
  (** Source for [derivation_context_vitali]: the condition that V is a phi
    Vitali relation in Federer 2.9.1, p. 152 *)
  derivation_context_vitali : is_vitali_relation phi V
}.
