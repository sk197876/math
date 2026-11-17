(** Federer (1969), 3.4.12, p. 339, extending 3.4.9, p. 337:
    the original family of all connected components of
    the difference of two holomorphic subvarieties is locally
    finite throughout the original open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness HolomorphicVarietyGermUP LocallyFiniteFamilyUP
  HolomorphicDifferenceLocalComponents ComponentImageLocalFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_families_local_finiteness]: the complete
    first assertion of 3.4.12, p. 339, extending 3.4.9, p. 337. Both
    sets retain the original local holomorphic definition;
    global finite equations are not assumed. *)
Theorem federer_3_4_12_families_local_finiteness (R:realType) n (U S D:set (coordinate_space (ComplexScalars.C R) n)):
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->@is_holomorphic_set_in R (coordinate_space (ComplexScalars.C R) n) NX hNX U S ->
  @is_holomorphic_set_in R (coordinate_space (ComplexScalars.C R) n) NX hNX U D ->
  @is_locally_finite_family_on T [the choiceType of (set T)] U
    (@connected_component T (S `\` D) @` (S `\` D)) (fun C=>C).
Proof.
move=>NX hNX T hU hS hD.
apply:component_image_locally_finite=>a ha.
exact:(@holomorphic_difference_local_components R n S D a (hS a ha) (hD a ha)).
Qed.
