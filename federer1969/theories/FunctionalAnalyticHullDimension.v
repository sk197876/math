(** Federer (1969), 3.4.10, p. 337:
    a lower-dimensional functional stratum has an
    analytic hull of no greater dimension.
    Apply the completed relative-open nullity theorem
    3.4.8(16), rather than repeating local algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticGermRing GermVanishingSealed
  AnalyticDepthSealed AnalyticVarietyGermUP FunctionalAnalyticSubmanifoldUP
  FunctionalAnalyticDifference FunctionalAnalyticManifold AnalyticSubmanifoldUP EuclideanSubmanifoldUP
  SubmanifoldCountablyRectifiable CountablyRectifiableHigherDegreeNull
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary FiniteAnalyticVarietyRelativeClosed
  Federer348RelativeOpenDimension IdealVarietyGermUP IdealVarietyGermExistence
  IdealVarietyGermSealed IdealVarietyVanishingLaws HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_hull_dimension]: the
    lower-dimensional analytic exceptional germs used in
    3.4.10, p. 337. The actual functional
    stratum is relatively open in its original
    equation variety; countable rectifiability supplies the
    required nullity in the next degree. *)
Theorem functional_analytic_hull_dimension (R:realType) n d
    (U S:set (R_n R n)):
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  U 0 ->@is_functional_analytic_submanifold R n d U S ->
  exists nu:@set_germ_space T 0,
    @is_analytic_variety_germ R (R_n R n) NX hNX 0%R nu /\
    set_germ_subset (@set_germ T 0%R S) nu /\
    (nu=@set_germ T 0%R set0 \/
      (@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) hB n
        (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
        (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0%R nu)<=d)%N).
Proof.
move=>hB NX hNX T hU0 hS.
have [H [N [hH [hN hEquation]]]]:=functional_analytic_difference hS.
have [C [hClosed hCEquation]]:=finite_analytic_variety_relative_closed_form hN.
have hHInside:H `<=` U:=finite_analytic_variety_domain_inside hH.
have hRelative:@relatively_open_set T H S.
  exists (~` C);split;first exact:closed_openC hClosed.
  rewrite hEquation hCEquation;apply/seteqP;split.
  - move=>x [hxH hxNot];split;first exact:hxH.
    move=>hxC;apply:hxNot;split;[exact:hHInside x hxH|exact:hxC].
  - move=>x [hxH hxNot];split;first exact:hxH.
    by move=>[_ hxC];exact:hxNot hxC.
have hHAnalytic:@is_analytic_variety_germ R (R_n R n) NX hNX 0%R (@set_germ T 0%R H).
  exists U,H;by split.
have hNull:@hausdorff_measure R (inner_metric_space hB) d.+1 S=0%E.
  apply:(@countably_rectifiable_higher_degree_null R n d d.+1 S (ltnSn d)).
  apply:(@submanifold_countably_rectifiable R n d 1%N S (leqnn 1)).
  exact:analytic_submanifold_class_one (functional_analytic_submanifold_analytic hS).
have [hI hDimension]:=@federer_3_4_8_16 R n H S d hHAnalytic hRelative hNull.
pose nu:=@IdealVarietyGerm.value R (R_n R n) NX hNX 0
  (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0%R (@set_germ T 0%R S)) hI.
exists nu;split.
- exact:(@ideal_variety_germ_is_variety R (R_n R n) NX hNX 0%R _ nu
    (@IdealVarietyGerm.laws R (R_n R n) NX hNX 0%R _ hI)).
split;last exact:hDimension.
exact:(@set_germ_in_variety_of_its_ideal R (R_n R n) NX hNX 0%R (@set_germ T 0%R S) hI).
Qed.
