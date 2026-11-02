(** Federer (1969), 2.9.10, p. 157: invariance of derivates under removal of
    the singular part and replacement of the Vitali relation. The Daniell
    observations in the same item are proved separately in
    DerivationDaniellMeasureClass.v, ContinuousPartLinfinity.v and
    DaniellDerivateRepresentation.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureAlmostUP MeasureDerivationContext
  AbsoluteContinuousPart ContinuousPartDecompositionUP MeasureRestriction MeasureDerivates
  DerivationUniqueness ContinuousSingularDerivates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_9_10]: direct first two displays
    in Federer 2.9.10, p. 157, collecting the continuous-part
    identity, zero singular derivate and Vitali-relation independence.
    The printed remainder notation denotes the complementary Borel
    restriction of 2.9.2; no infinity subtraction is performed.
    The two later Daniell observations have separate named theorems. *)
Theorem federer_2_9_10 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_almost_equal phi (measure_derivate (measure_continuous_part psi phi) phi V)
    (measure_derivate psi phi V) /\
  (forall B, is_continuous_part_decomposition phi psi (measure_continuous_part psi phi) B ->
    measure_almost_everywhere phi [set x |
      partial_function_graph (measure_derivate (measure_restrict psi (~` B)) phi V) x 0]) /\
  (forall W, is_measure_derivation_context phi W ->
    measure_almost_equal phi (measure_derivate psi phi V) (measure_derivate psi phi W)).
Proof.
move=> hc hpsi; split.
- exact: continuous_part_derivate_equal hc hpsi.
- split.
  + move=> B hB; exact: singular_remainder_derivate_zero hc hpsi hB.
  + move=> W hW; exact: derivate_independent_vitali_relation hc hW hpsi.
Qed.
