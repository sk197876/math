(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    the induction is simultaneous in every finite
    ambient dimension. The construction may keep each
    actual stratum inside the given holomorphic representative.
    This existence invariant supplies the local component
    consequence used at the smaller critical depths. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP FiniteHolomorphicVarietyUP
  HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_stratification_at_bound]:
    the original induction statement for (11), p. 333,
    strengthened to retain the actual representative and
    allow an upper dimension bound. These are independent
    existence requirements, not an assumed stratification theorem. *)
Definition holomorphic_stratification_at_bound (R:realType) (m:nat):Prop:=
  forall n (U H U0 S0:set (coordinate_space (ComplexScalars.C R) n)),
    let NX:=@holomorphic_coordinate_norm R n in
    let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
    let T:=Topological.clone (real_norm_metric_space hNX) _ in
    let germ:=@set_germ T 0 in
    let depth:=@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n)
      (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
      (dual_basis (@coordinate_basisP (ComplexScalars.C R) n)) in
    U 0 ->@is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) NX hNX U H ->
    U0 0 ->@is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) NX hNX U0 S0 ->
    (depth (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H))<=m)%N ->
    exists mu,exists V S G:'I_mu->set (coordinate_space (ComplexScalars.C R) n),
      @is_holomorphic_finite_stratification R n (germ H) (germ S0) m U0 S0 mu V S G /\
      forall i,S i `<=` H.
