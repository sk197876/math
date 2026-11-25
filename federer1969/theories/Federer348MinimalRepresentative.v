(** Federer (1969), 3.4.8(12), pp. 327, 335:
    every original analytic variety germ has a representative
    contained in every analytic subvariety of the prescribed
    neighbourhood whose germ contains it. The complete
    stratification supplies the finite component family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  SetGermSealed SetGermLaws SetGermOrder AnalyticVarietyGermUP FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyBoundary GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticFiniteStratificationExistence AnalyticMinimalRepresentativeUP AnalyticMinimalRepresentativeAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MinimalRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ E 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [federer_3_4_8_12]: every assertion of
    (12), p. 327, with the printed component
    selection and continuation proof, p. 335. The
    empty germ and zero ambient dimension remain included. *)
Theorem federer_3_4_8_12 (alpha:@set_germ_space E 0) (U:set X):
  @is_analytic_variety_germ R X NX hNX 0 alpha ->@open E U ->U 0 ->
  exists S:set X,@is_analytic_minimal_representative R n alpha U S.
Proof.
move=>[W [H [hW0 [hH hAlpha]]]] hU hU0.
have hEmpty:=@finite_analytic_variety_domain_empty R X NX hNX U hU.
pose d:=depth (ideal (germ H)).
have [mu [V [S [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R d n
  W H U set0 hW0 hH hU0 hEmpty (leqnn d).
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation E 0 _ _ _ (@SetGerms.laws E 0)) setC0
  (@set_germ_intersection_equation E 0 _ _ _ (@SetGerms.laws E 0)) setIT hAlpha in hGerm.
apply:(@analytic_minimal_representative_from_strata R n alpha U mu V S).
- move=>i;have hV:=analytic_stratification_neighbourhoods hLaws i;split;[exact:hV.1|exact:hV.2.2].
- move=>i;have [e [he hMan]]:=analytic_stratification_functional hLaws i;by exists e.
- exact:analytic_stratification_components hLaws.
- exact:esym hGerm.
Qed.
End MinimalRepresentative.
