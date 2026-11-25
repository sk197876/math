(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(12), pp. 327, 335:
    every original holomorphic variety germ has a representative
    contained in every holomorphic subvariety of the prescribed
    neighbourhood whose germ contains it. The complete
    stratification supplies the finite component family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  SetGermSealed SetGermLaws SetGermOrder HolomorphicVarietyGermUP FiniteHolomorphicVarietyUP
  FiniteHolomorphicVarietyBoundary HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP
  HolomorphicFiniteStratificationExistence HolomorphicMinimalRepresentativeUP HolomorphicMinimalRepresentativeAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MinimalRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ E 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [federer_3_4_12_12]: every assertion of
    (12), p. 327, with the printed component
    selection and continuation proof, p. 335. The
    empty germ and zero ambient dimension remain included. *)
Theorem federer_3_4_12_12 (alpha:@set_germ_space E 0) (U:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->@open E U ->U 0 ->
  exists S:set X,@is_holomorphic_minimal_representative R n alpha U S.
Proof.
move=>[W [H [hW0 [hH hAlpha]]]] hU hU0.
have hEmpty:=@finite_holomorphic_variety_domain_empty R X NX hNX U hU.
pose d:=depth (ideal (germ H)).
have [mu [V [S [G [hLaws hInside]]]]]:=@holomorphic_finite_stratification_exists_at_bound R d n
  W H U set0 hW0 hH hU0 hEmpty (leqnn d).
have hGerm:=holomorphic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation E 0 _ _ _ (@SetGerms.laws E 0)) setC0
  (@set_germ_intersection_equation E 0 _ _ _ (@SetGerms.laws E 0)) setIT hAlpha in hGerm.
apply:(@holomorphic_minimal_representative_from_strata R n alpha U mu V S).
- move=>i;have hV:=holomorphic_stratification_neighbourhoods hLaws i;split;[exact:hV.1|exact:hV.2.2].
- move=>i;have [e [he hMan]]:=holomorphic_stratification_functional hLaws i;by exists e.
- exact:holomorphic_stratification_components hLaws.
- exact:esym hGerm.
Qed.
End MinimalRepresentative.
