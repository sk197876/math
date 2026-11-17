(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    a variety germ of dimension at most k
    has a compact representative of finite H^(2k) mass.
    Use the original irreducible decomposition and the
    compact representatives already proved in 3.4.8(13).
    No new rectifiability or measure theorem is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HolomorphicGrowthRepresentative FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermFiniteUnion
  HolomorphicGermRing HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicVarietyGermUP HolomorphicIrreducibleGermUP HolomorphicGermNoetherian
  HolomorphicIrreducibleGermCoverUP NoetherianHolomorphicIrreducibleCover HolomorphicIdealDepthMonotonicity
  HolomorphicGrowthRepresentative RectifiableSetUP HausdorffMeasure
  HausdorffDimensionDrop MeasureUP MeasureBasic MeasureFiniteUnionMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteMassRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation hB:=(hermitian_real_inner_product (@standard_hermitian_productP R n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).
Local Notation G:=(@set_germ_space T 0).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_germ_finite_mass_representative]: the
    local finite-mass input to 3.4.10, p. 337.
    It retains arbitrary natural degree above the actual
    germ dimension, arbitrary reducible germs and the
    empty germ. The compact representative is an existence
    witness; its construction is not a public definition. *)
Theorem holomorphic_germ_finite_mass_representative (alpha:G) k:
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->
  (depth (ideal alpha)<=k)%N ->
  exists S:set X,@compact E S /\germ S=alpha /\
    (@hausdorff_measure R E (k+k) S< +oo)%E.
Proof.
move=>hAlpha hBound.
case:(pselect (alpha=germ set0))=>hEmpty.
- exists set0;split;first exact:compact0.
  split;first exact:esym hEmpty.
  by rewrite (measure_empty (@hausdorff_measure_is_measure R E (k+k))) lt0y.
- have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=
    @holomorphic_growth_representative R n alpha hAlpha hEmpty.
  exists S;split;first exact:hCompact.
  split;first exact:hGerm.
  case:(eqVneq (depth (ideal alpha)) k)=>hEqual.
  + rewrite -hEqual;exact:hRect.2.
  + have hStrict:(depth (ideal alpha)<k)%N by rewrite ltn_neqAle hEqual hBound.
    have hDoubled:(depth (ideal alpha)+depth (ideal alpha)<k+k)%N by rewrite !addnn ltn_double.
    have hNull:=@hausdorff_finite_mass_higher_degree_zero R E
      (depth (ideal alpha)+depth (ideal alpha)) (k+k) S hDoubled hRect.2.
    by rewrite hNull lt0y.
Qed.
End FiniteMassRepresentative.
