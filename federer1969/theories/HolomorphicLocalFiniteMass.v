(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    transfer the compact finite-mass germ representative
    to the actual original set near its centre.
    Use the proved equality-on-a-neighbourhood law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermExistence HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicGermFiniteMassRepresentative HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_origin_local_finite_mass]: the local
    measure bound underlying the first assertion of
    3.4.10, p. 337. Neither the original
    set nor its finite-mass representative is assumed
    measurable; equal germs provide the actual inclusion. *)
Theorem holomorphic_origin_local_finite_mass (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)) k:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R S) ->
  (@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
    (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R S))<=k)%N ->
  exists W:set (coordinate_space (ComplexScalars.C R) n),@open T W /\W 0 /\
    (@hausdorff_measure R (inner_metric_space hB) (k+k) (S `&` W)< +oo)%E.
Proof.
move=>hB NX hNX T hHolomorphic hBound.
have [A [hCompact [hGerm hMass]]]:=@holomorphic_germ_finite_mass_representative R n
  (@set_germ T 0%R S) k hHolomorphic hBound.
have [W [hW [hW0 hEqual]]]:=(@set_germ_equality_original T 0 A S).1 hGerm.
exists W;split;first exact:hW.
split;first exact:hW0.
apply:(le_lt_trans (@measure_mono R (inner_metric_space hB)
  (@hausdorff_measure R (inner_metric_space hB) (k+k))
  (@hausdorff_measure_is_measure R (inner_metric_space hB) (k+k)) (S `&` W) A _) hMass).
move=>x hx;have h:=(hx:(S `&` W) x);by rewrite -hEqual in h;exact:h.1.
Qed.
