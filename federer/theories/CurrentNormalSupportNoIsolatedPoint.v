(** Federer (1969), 4.1.12, p. 368: local
    normal one-currents on the line have no isolated
    support points. Localise by the actual compact
    scalar cutoff and use the preceding point-support
    vanishing theorem. This is sufficient for the
    exact endpoint set of the first example. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentSpaces CurrentContraction CurrentContractionSupport CurrentContractionCompactSupport CurrentSupportGeometry
  CurrentSupportAgreement CurrentScalarPlateau NormalCurrentsUP LocallyNormalScalarContraction
  CurrentNormalPointSupportZero CurrentNeighbourhoodCutoff SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalSupportNoIsolatedPoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable T:@current_space R h2 1%N U hU 1%N.
Hypothesis hNormal:@is_locally_normal_current R h2 1%N U hU 1%N T.
Local Notation support := (@current_support R h2 1%N U hU 1%N).
Local Notation hE0 := (@current_smooth_space_laws R h2 1%N U hU 0%N).

(** Source for [current_normal_isolated_support_exclusion]:
    if an open neighbourhood W meets the support
    of a locally normal one-current only at x,
    then x is outside that support. This supporting
    consequence of 4.1.7, p. 358, and compact
    top-degree uniqueness proves the support obstruction in
    Federer 4.1.12, p. 368, for its original
    endpoint set. No mass density is assumed. *)
Theorem current_normal_isolated_support_exclusion x (W:set X):
  @open XT W->W x->(forall y,support T y->W y->y=x)->~support T x.
Proof.
move=>hW hWx hIsolated hx.
have hOpenU:@open XT U.
  rewrite openE=>y hy.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U y).1.
  exact:(hU y hy).
pose K:=@smooth_compact_singleton R X NX hNX U x hx.1.
have hKW:smooth_compact_carrier K `<=` W `&` U.
  move=>y ->;split;first exact:hWx.
  exact:hx.1.
have[gamma [hGamma [V [hV [hKV [hVW hOne]]]]]]:=
  @current_neighbourhood_scalar_cutoff R h2 1%N U hU K (W `&` U)
    (openI hW hOpenU) hKW (fun y hy=>hy.2).
pose a:=smooth_test_inclusion hE0 gamma.
pose Q:=@current_contraction R h2 1%N 0%N 1%N U hU a T.
have hNormalQ:=@locally_normal_compact_scalar_contraction R h2 1%N U hU 1%N gamma T hNormal.
pose KG:=@Build_smooth_compact_set R X NX hNX U
  (@current_test_support R h2 1%N 0%N U hU gamma) (fun y hy=>hy.1)
  (smooth_test_support_compact hE0 gamma).
have hQSupport:support Q `<=` [set x].
  move=>y hy.
  have hTSupport:=@current_contraction_support_subset R h2 1%N 0%N 1%N U hU a T y hy.
  have hGSupport:=@current_contraction_support_compact_bound R h2 1%N 0%N 1%N U hU
    KG a T (fun z hz=>hz) y hy.
  exact:(hIsolated y hTSupport (hGamma y hGSupport).1).
have hZero:Q=0:=@current_normal_point_support_zero R h2 U hU Q x hNormalQ hQSupport.
have hAgree:forall psi:@current_test_space R h2 1%N U hU 1%N,
    @current_test_support R h2 1%N 1%N U hU psi `<=` V->
    @current_value R h2 1%N U hU 1%N T psi=@current_value R h2 1%N U hU 1%N Q psi.
  move=>psi hPsi;rewrite current_contraction_evaluation.
  by rewrite (@current_scalar_test_local_plateau R h2 1%N 1%N U hU V a hOne psi hPsi).
have hOutside:=@current_support_difference_agreement R h2 1%N 1%N U hU T Q V hV hAgree.
rewrite hZero GRing.Theory.subr0 in hOutside.
exact:(hOutside x hx).2 (hKV x (erefl x)).
Qed.
End CurrentNormalSupportNoIsolatedPoint.
