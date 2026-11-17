(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    identify the translated local ideal depth with
    the original opaque nonempty germ dimension
    of 3.4.8(3), p. 326. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  HolomorphicVarietyGermUP HolomorphicSetLocalDepth HolomorphicVarietyGermDimensionSealed
  HolomorphicVarietyGermDimensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_local_depth_original_dimension]: the
    exact original local dimension in the
    supremum of 3.4.10, p. 337.
    Translate the actual centre to zero and
    apply the proved equality with ideal depth;
    the result is independent of both holomorphic
    and nonempty-germ proof witnesses. *)
Theorem holomorphic_set_local_depth_original_dimension (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)) a:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  forall hA:@is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (@set_germ T 0 [set x|S (a+x)]),
  forall hNonempty:@set_germ T 0 [set x|S (a+x)]<>@set_germ T 0 set0,
  @holomorphic_set_local_depth R n S a=
    @HolomorphicVarietyGermDimension.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
      (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
      (@set_germ T 0 [set x|S (a+x)]) hA hNonempty.
Proof.
move=>hB NX hNX T hA hNonempty.
exact:esym (@holomorphic_variety_germ_dimension_depth R (coordinate_space (ComplexScalars.C R) n)
  (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n)
  (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
  (@set_germ T 0 [set x|S (a+x)]) hA hNonempty).
Qed.
