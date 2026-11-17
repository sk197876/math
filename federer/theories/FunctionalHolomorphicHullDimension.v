(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    a lower-dimensional functional stratum has an
    holomorphic hull of no greater dimension.
    Apply the completed relative-open nullity theorem
    3.4.8(16), rather than repeating local algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import HolomorphicSubmanifoldHigherDegreeNull FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder HolomorphicGermRing HolomorphicGermVanishingSealed
  HolomorphicDepthSealed HolomorphicVarietyGermUP FunctionalHolomorphicSubmanifoldUP
  FunctionalHolomorphicDifference FunctionalHolomorphicManifold HolomorphicSubmanifoldUP EuclideanSubmanifoldUP
  SubmanifoldCountablyRectifiable CountablyRectifiableHigherDegreeNull
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyBoundary FiniteHolomorphicVarietyRelativeClosed
  Federer3412RelativeOpenDimension HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermExistence
  HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_hull_dimension]: the
    lower-dimensional holomorphic exceptional germs used in
    3.4.10, p. 337. The actual functional
    stratum is relatively open in its original
    equation variety; countable rectifiability supplies the
    required nullity in the next degree. *)
Theorem functional_holomorphic_hull_dimension (R:realType) n d
    (U S:set (coordinate_space (ComplexScalars.C R) n)):
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  U 0 ->@is_functional_holomorphic_submanifold R n d U S ->
  exists nu:@set_germ_space T 0,
    @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R nu /\
    set_germ_subset (@set_germ T 0%R S) nu /\
    (nu=@set_germ T 0%R set0 \/
      (@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
        (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
        (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R nu)<=d)%N).
Proof.
move=>hB NX hNX T hU0 hS.
have [H [N [hH [hN hEquation]]]]:=functional_holomorphic_difference hS.
have [C [hClosed hCEquation]]:=finite_holomorphic_variety_relative_closed_form hN.
have hHInside:H `<=` U:=finite_holomorphic_variety_domain_inside hH.
have hRelative:@relatively_open_set T H S.
  exists (~` C);split;first exact:closed_openC hClosed.
  rewrite hEquation hCEquation;apply/seteqP;split.
  - move=>x [hxH hxNot];split;first exact:hxH.
    move=>hxC;apply:hxNot;split;[exact:hHInside x hxH|exact:hxC].
  - move=>x [hxH hxNot];split;first exact:hxH.
    by move=>[_ hxC];exact:hxNot hxC.
have hHHolomorphic:@is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R H).
  exists U,H;by split.
have hNull:@hausdorff_measure R (inner_metric_space hB) (d+d).+2 S=0%E.
  apply:(@holomorphic_submanifold_higher_degree_null R n d (d+d).+2 S (ltn_trans (ltnSn (d+d)) (ltnSn (d+d).+1))).
  exact:functional_holomorphic_submanifold_holomorphic hS.
have [hI hDimension]:=@federer_3_4_12_16 R n H S d hHHolomorphic hRelative hNull.
pose nu:=@HolomorphicIdealVarietyGerm.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0
  (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R S)) hI.
exists nu;split.
- exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R _ nu
    (@HolomorphicIdealVarietyGerm.laws R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R _ hI)).
split;last exact:hDimension.
exact:(@HolomorphicIdealVarietyVanishingLaws.set_germ_in_variety_of_its_ideal R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R S) hI).
Qed.
