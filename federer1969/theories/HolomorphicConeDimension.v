(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.11, p. 338:
    the global dimension of the homogeneous polynomial
    majorant is bounded by its original germ dimension
    at zero. The existing stratification supplies a null
    germ representative; positive dilation and the proved
    global null-dimension connection finish the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicVarietyGermUP
  HolomorphicSetDimension HolomorphicGermOriginalNull InnerConeGlobalNull HolomorphicNullSetDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_cone_global_dimension_bound]: the
    literal global dimension bound of the homogeneous
    polynomial majorant in 3.4.11, p. 338.
    The source cone may be reducible, and every
    finite ambient dimension, including zero, remains. *)
Theorem holomorphic_cone_global_dimension_bound (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)):
  let X:=coordinate_space (ComplexScalars.C R) n in
  let B:=@standard_hermitian_product R n in
  let hB:=@standard_hermitian_productP R n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let d:=@HolomorphicDepth.value R X B hB n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
    (dual_basis (@coordinate_basisP (ComplexScalars.C R) n)) (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 S)) in
  @is_holomorphic_set_in R X NX hNX setT S ->
  (forall t:R,0<t ->forall x,S x ->S (t*:(x:restricted_space (ComplexScalars.embed R) X))) ->
  (@holomorphic_set_dimension R n S<=d)%N.
Proof.
move=>X B hB NX hNX T d hHolomorphic hCone.
have [A [hGerm hNull]]:=@holomorphic_germ_original_null_representative R n
  (@set_germ T 0 S) (d+d).+2 (hHolomorphic 0 Logic.I) (ltn_trans (ltnSn (d+d)) (ltnSn (d+d).+1)).
apply:(@holomorphic_null_set_dimension_bound R n S d hHolomorphic).
exact:(@inner_cone_global_null_from_germ R (restricted_space (ComplexScalars.embed R) X)
  (hermitian_real_part B) (hermitian_real_inner_product hB) hNX S A (d+d).+2 hCone hGerm hNull).
Qed.
