(** Abstract decomposition conclusions of Federer (1969), 2.9.2, p. 153. The
    remaining measure is expressed by restriction to the complement; the sum
    law makes sense even at infinite values. Source context:
    MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureAbsoluteContinuity MeasureRestriction TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_continuous_part_decomposition]: direct
    abstract specification of the conclusions of Federer 2.9.2,
    p. 153. The printed remaining part psi-psi_phi
    is represented by psi restricted to the complement of B;
    a sum identity avoids undefined infinity-minus-infinity arithmetic. *)
Record is_continuous_part_decomposition (R : realType) (X : metricType R)
    (phi psi gamma : set X -> \bar R) (B : set X) : Prop := {
  (** Source for [continuous_decomposition_borel]: B is
      Borel in Federer 2.9.2, p. 153. *)
  continuous_decomposition_borel : borel_set B;
  (** Source for [continuous_decomposition_conull]: the
      complement of B is phi-null in Federer 2.9.2,
      p. 153. *)
  continuous_decomposition_conull : phi (setT `\` B)=0;
  (** Source for [continuous_decomposition_restriction]: the
      restriction identity in Federer 2.9.2, p. 153. *)
  continuous_decomposition_restriction : gamma=measure_restrict psi B;
  (** Source for [continuous_decomposition_class]: psi_phi
      belongs to M, Federer 2.9.2, p. 153. *)
  continuous_decomposition_class : is_derivation_measure gamma;
  (** Source for [continuous_decomposition_remaining_class]:
      the complementary restriction belongs to M in Federer
      2.9.2, p. 153. *)
  continuous_decomposition_remaining_class : is_derivation_measure (measure_restrict psi (~` B));
  (** Source for [continuous_decomposition_sum]: precise
      additive interpretation of the remaining-part notation in
      Federer 2.9.2, p. 153. Infinite values are allowed. *)
  continuous_decomposition_sum : forall A, psi A=gamma A+measure_restrict psi (~` B) A;
  (** Source for [continuous_decomposition_absolute]: absolute continuity of
    the continuous part in Federer 2.9.2, p. 153 *)
  continuous_decomposition_absolute : is_absolutely_continuous_measure gamma phi
}.
