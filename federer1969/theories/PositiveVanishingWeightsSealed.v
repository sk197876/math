(** Opaque choice of weights for Federer (1969), 2.4.10, p. 85, through the
    abstract hypotheses of 2.3.3, p. 76. Downstream characteristic
    expansions depend only on those hypotheses. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import WeightedCharacteristicExpansionUP HarmonicWeightsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type PositiveVanishingWeightsSignature.
(** Source for [value]: weights for the characteristic expansion
    invoked in Federer 2.4.10, p. 85. *)
Parameter value : forall R : realType, nat -> R.
(** Source for [laws]: the three hypotheses of 2.3.3,
    p. 76, used in Federer 2.4.10, p. 85. *)
Parameter laws : forall R : realType, is_positive_vanishing_divergent_sequence (@value R).
End PositiveVanishingWeightsSignature.
Module PositiveVanishingWeights : PositiveVanishingWeightsSignature.
(** Source for [value]: private selection of the proved
    weight witness for Federer 2.4.10, p. 85. *)
Definition value (R : realType) := projT1 (cid (positive_vanishing_divergent_weights_exist R)).
(** Source for [laws]: selected witness satisfies the abstract
    weight hypotheses used in Federer 2.4.10, p. 85. *)
Lemma laws (R : realType) : is_positive_vanishing_divergent_sequence (@value R).
Proof. exact: projT2 (cid (positive_vanishing_divergent_weights_exist R)). Qed.
End PositiveVanishingWeights.
