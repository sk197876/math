(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), p. 335:
    the original analytic variety germ has a representative
    null at every integer degree above its actual depth.
    This is the upper half of the dimension comparison,
    proved by the complete stratification (11). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import AnalyticVarietyGermRecovery EuclideanSubmanifoldUP SetGermExistence SetGermBoundary SetGermOrder IdealVarietyGermSealed IdealVarietyVanishingLaws IdealVarietyGermUP Federer348RelativeOpenDimension MeasureAlmostBasic RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws AnalyticVarietyGermUP FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyBoundary GermVanishingSealed AnalyticDepthSealed
  AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence AnalyticStrataHigherDegreeNull
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NullRepresentative.
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

(** Source for [analytic_null_representative_depth_bound]: the
    real-case dimension comparison used in 3.4.12, p. 339.
    Apply the already proved relative-open hull theorem,
    3.4.8(16), p. 337, on the actual neighbourhood
    where the original analytic and null representatives agree. *)
Theorem analytic_null_representative_depth_bound (alpha:@set_germ_space E 0)
    (A:set X) u:
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  alpha<>germ set0 ->germ A=alpha ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) u.+1 A=0%E ->
  (depth (ideal alpha)<=u)%N.
Proof.
move=>[U [S [hU0 [hS hSGerm]]]] hNonempty hAGerm hNull.
have hSame:germ S=germ A by rewrite hSGerm hAGerm.
move/set_germ_equality_original:hSame=>[W [hW [hW0 hEquality]]].
pose D:=S `&` W.
have hDSubset:D `<=` A.
  move=>x hx;have hAx:(A `&` W) x by rewrite -hEquality.
  exact:hAx.1.
have hDNull:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) u.+1 D=0%E.
  exact:(@measure_null_subset R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) u.+1)
    (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) u.+1)
    D A hDSubset hNull).
have hDRelative:@relatively_open_set E S D by exists W;split=>//;rewrite setIC.
have hDGerm:germ D=alpha.
  apply:(eq_trans _ hSGerm);apply/set_germ_equality_original;exists W;split=>//.
  by split=>//;rewrite /D -setIA setIid.
have hSGermVariety:@is_analytic_variety_germ R X NX hNX 0 (germ S).
  exists U,S;by split=>//;split.
have [hI hDimension]:=@federer_3_4_8_16 R n S D u hSGermVariety hDRelative hDNull.
have hDVariety:@is_analytic_variety_germ R X NX hNX 0 (germ D).
  rewrite hDGerm;exists U,S;by split=>//;split.
have hRecovery:=@analytic_variety_germ_ideal_recovery R X NX hNX 0 (germ D) hI hDVariety.
cbn zeta in hDimension.
rewrite -hRecovery hDGerm in hDimension.
case:hDimension=>// hEmpty;exfalso;exact:hNonempty hEmpty.
Qed.
End NullRepresentative.
