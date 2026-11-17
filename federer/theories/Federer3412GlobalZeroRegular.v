(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    a zero-dimensional holomorphic set has no
    nonregular part. This states the endpoint
    without extending Hausdorff measure to negative degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicVarietyGermUP
  HolomorphicSetLocalDepth HolomorphicSetDimension BoundedNaturalSupremumUP
  HolomorphicRegularLocusUP HolomorphicRegularLocusSealed HolomorphicCentreZeroRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_global_zero_regular]: the
    dimension-zero endpoint of the regular-part
    assertion of 3.4.10, p. 337.
    The actual opaque regular part equals S. *)
Theorem federer_3_4_12_global_zero_regular (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)):
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_holomorphic_set_in R (coordinate_space (ComplexScalars.C R) n) (inner_norm hB) hNX U S ->
  @holomorphic_set_dimension R n S=0%N ->
  @HolomorphicRegularLocus.value R n 0 U S=S.
Proof.
move=>hB hNX T hU hSU hHolomorphic hDimension.
apply/seteqP;split.
- move=>a /(HolomorphicRegularLocus.laws)=>h;exact:h.1.
- move=>a haS.
  have hBound:(@holomorphic_set_local_depth R n S a<=0)%N.
    rewrite -hDimension.
    exact:(@bounded_natural_supremum_upper (coordinate_space (ComplexScalars.C R) n) S
      (@holomorphic_set_local_depth R n S) (@holomorphic_set_dimension R n S)
      (@holomorphic_set_dimension_laws R n S) a haS).
  exact:(@holomorphic_centre_zero_regular R n U S
    (@HolomorphicRegularLocus.value R n 0 U S) a hU (hSU a haS)
    (hHolomorphic a (hSU a haS)) hBound (@HolomorphicRegularLocus.laws R n 0 U S) haS).
Qed.
