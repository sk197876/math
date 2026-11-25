(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    dominate a local exceptional set by a compact
    finite-mass representative of its smaller-dimensional
    holomorphic hull. Keep an empty hull separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicGermFiniteMassRepresentative HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_compact_domination]: the local
    exceptional-set mass bound in 3.4.10, p. 337.
    Only a proved smaller-dimensional holomorphic containing
    germ is supplied. The compact finite-mass set
    is then constructed by the earlier representative
    theorem, with no measurability premise. *)
Theorem holomorphic_germ_compact_domination (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)) k:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  forall nu:@set_germ_space T 0,
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 nu ->
  set_germ_subset (@set_germ T 0 S) nu ->
  (nu=@set_germ T 0 set0 \/
    (@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
      (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
      (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R nu)<=k)%N) ->
  exists K:set (coordinate_space (ComplexScalars.C R) n),@compact (inner_metric_space hB) K /\
    set_germ_subset (@set_germ T 0 S) (@set_germ T 0 K) /\
    (@hausdorff_measure R (inner_metric_space hB) (k+k) K< +oo)%E.
Proof.
move=>hB NX hNX T nu hNu hContained [hEmpty|hDimension].
- exists set0;split;first exact:compact0.
  split;first by rewrite -hEmpty.
  by rewrite (measure_empty (@hausdorff_measure_is_measure R (inner_metric_space hB) (k+k))) lt0y.
- have [K [hCompact [hGerm hMass]]]:=@holomorphic_germ_finite_mass_representative R n nu k hNu hDimension.
  exists K;split;first exact:hCompact.
  split;last exact:hMass.
  by rewrite hGerm.
Qed.
