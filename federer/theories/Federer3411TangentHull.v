(** Federer (1969), 3.4.11, p. 338:
    the complete original tangent-hull dimension assertion
    at the original centre. Every dimension is the
    original opaque nonempty variety-germ dimension; actual
    translation and tangent locality supply the reduction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AnalyticGermRing CommutativeIdealUP SetGermUP SetGermOrder SetGermBoundary SetGermCentreMember
  GermVanishingSealed AnalyticVarietyGermUP AnalyticSetNonemptyCentres AnalyticSetLocalDepth
  AnalyticDepthSealed AnalyticVarietyGermDimensionSealed AnalyticVarietyGermDimensionLaws
  IdealVarietyGermSealed TangentConeUP TangentConeBasic TangentConeTranslation
  AnalyticTangentHullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_11]: the first original
    dimension display of 3.4.11, p. 338.
    Original open U, analytic S, centre a and
    nonempty source germ remain. The actual tangent hull,
    both nonempty analytic germs and the finite ideal
    witnesses are constructed internally. *)
Theorem federer_3_4_11 (R:realType) n (U S:set (R_n R n)) a:
  let X:=R_n R n in
  let B:=@euclidean_inner_product R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let e:=@coordinate_basis R n in
  let he:=@coordinate_basisP R n in
  let omega:=dual_basis he in
  @open T U ->S `<=` U ->@is_analytic_set_in R X NX hNX U S ->U a ->
  @set_germ T a S<>@set_germ T a set0 ->
  exists hSource:@is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0 [set x|S (a+x)]),
  exists hNonempty:@set_germ T 0 [set x|S (a+x)]<>@set_germ T 0 set0,
  exists hJ:@is_finitely_generated_commutative_ideal
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]
    (@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 (norm_tangent_cone NX S a))),
  let nu:=@IdealVarietyGerm.value R X NX hNX 0
    (@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 (norm_tangent_cone NX S a))) hJ in
  exists hNu:@is_analytic_variety_germ R X NX hNX 0 nu,
  exists hNuNonempty:nu<>@set_germ T 0 set0,
    set_germ_subset (@set_germ T 0 (norm_tangent_cone NX S a)) nu /\
    (@AnalyticVarietyGermDimension.value R X B hB n e he omega nu hNu hNuNonempty<=
      @AnalyticVarietyGermDimension.value R X B hB n e he omega
        (@set_germ T 0%R [set x|S ((a+x)%R)]) hSource hNonempty)%N.
Proof.
move=>X B hB NX hNX T e he omega hU hSU hAnalytic haU hSourceNonempty.
have haS:=(@analytic_set_nonempty_germ_centres R X NX hNX U S a hAnalytic haU).1 hSourceNonempty.
have hSource:=@analytic_set_translated_germ R n S a (hAnalytic a haU).
have hNonempty:=@analytic_set_translated_nonempty R n S a haS.
have hHull:=@analytic_tangent_hull_depth_bound R n [set x|S (a+x)] hSource hNonempty.
rewrite (@norm_tangent_source_translation R X NX S a) in hHull.
have [hJ [hNu [hContain hBound]]]:=hHull.
exists hSource,hNonempty,hJ.
pose nu:=@IdealVarietyGerm.value R X NX hNX 0
  (@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 (norm_tangent_cone NX S a))) hJ.
have hTangentZero:norm_tangent_cone NX S a 0.
  apply:(@norm_tangent_zero_closure R X NX hNX S a).2.
  exact:(@subset_closure T S a haS).
have hTangentNonempty:=@set_germ_centre_member_nonempty T 0
  (norm_tangent_cone NX S a) hTangentZero.
have hNuNonempty:nu<>@set_germ T 0 set0.
  move=>hEmpty;apply:hTangentNonempty;apply:set_germ_subset_empty.
  by rewrite -hEmpty.
exists hNu,hNuNonempty;split;first exact:hContain.
rewrite !analytic_variety_germ_dimension_depth;exact:hBound.
Qed.
