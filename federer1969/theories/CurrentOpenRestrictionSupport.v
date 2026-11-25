(** Federer (1969), 4.1.13, pp. 369–370: replacing U
    by a neighbourhood of spt T preserves the original
    support. More generally, open restriction intersects support
    with the smaller open domain. Use the proved range of
    actual test zero extension from 4.1.4, p. 348. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry
  CurrentOpenRestriction CurrentOpenRestrictionLocality FunctionalSupportUP
  NormBoundedLinearTopology SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  TestZeroExtensionUP TestZeroExtensionSealed TestZeroExtensionRange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentOpenRestrictionSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation XT := (real_norm_metric_space hNX).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x->V x.
Local Notation EU := (@current_smooth_space R h2 n U hU m).
Local Notation EV := (@current_smooth_space R h2 n V hV m).
Local Notation evU := (@current_smooth_value R h2 n U hU m).
Local Notation evV := (@current_smooth_value R h2 n V hV m).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hEV := (@current_smooth_space_laws R h2 n V hV m).
Local Notation DU := (@current_test_space R h2 n U hU m).
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation supportU := (@current_test_support R h2 n m U hU).
Local Notation supportV := (@current_test_support R h2 n m V hV).
Local Notation P := (@current_open_test_extension R h2 n m U V hU hV hUV).
Local Notation hP := (@TestZeroExtension.laws R X Y NX NY hNX hNY
  U V hV hUV EU EV evU evV hEU hEV).

(** Source for [current_open_test_extension_supported_range]:
    every original V-test supported in U is a zero
    extension of a U-test, by Federer 4.1.4,
    p. 348. This supports the source-neighbourhood
    replacement in 4.1.13, pp. 369–370. *)
Theorem current_open_test_extension_supported_range (phi:DV):
  supportV phi `<=` U->exists psi:DU,P psi=phi.
Proof.
exact:(@test_zero_extension_range R X Y NX NY hNX hNY
  U V hU hUV EU EV evU evV hEU hEV P hP phi).
Qed.

Variable T:@current_space R h2 n V hV m.
Local Notation S := (@current_open_restriction R h2 n m U V hU hV hUV T).

(** Source for [current_open_restriction_support_subset]:
    restriction cannot introduce an original support point,
    by 4.1.1, p. 344, supporting the smaller
    neighbourhood in Federer 4.1.13, pp. 369–370. *)
Theorem current_open_restriction_support_subset:
  @current_support R h2 n U hU m S `<=`
    @current_support R h2 n V hV m T.
Proof.
move=>x [hx hNot];split;first exact:hUV x hx.
move=>[W [[hW hZero] hWx]].
apply:hNot;exists W;split;last exact:hWx.
split;first exact:hW.
move=>psi hPsi;rewrite current_open_restriction_evaluation.
apply:hZero.
change (supportV (P psi) `<=` W).
rewrite (@CurrentOpenRestrictionLocality.current_open_test_extension_support
  R h2 n m U V hU hV hUV psi).
exact:hPsi.
Qed.

(** Source for [current_open_restriction_support]: the exact
    support of the original open restriction is U intersect
    spt T, by the support definition of 4.1.1,
    p. 344. In particular, Federer's replacement of the
    source by a neighbourhood in 4.1.13, pp. 369–370,
    leaves the original support unchanged. *)
Theorem current_open_restriction_support:
  @current_support R h2 n U hU m S=
    U `&` @current_support R h2 n V hV m T.
Proof.
apply:funext=>x;apply:propext;split.
- move=>hx;split;first exact:hx.1.
  exact:current_open_restriction_support_subset hx.
- move=>[hUx hTx];split;first exact:hUx.
  move=>[W [[hW hZero] hWx]].
  have hUOpen:@open XT U.
    rewrite openE=>z hz.
    exact:((@norm_domain_interior_neighbourhood R X NX hNX U z).1 (@hU z hz)).
  apply:hTx.2;exists (W `&` U);split;last exact:conj hWx hUx.
  split;first exact:openI hW hUOpen.
  move=>phi hPhi.
  have [psi hPsi]:=current_open_test_extension_supported_range (phi:=phi)
    (fun z hz=>(hPhi z hz).2).
  rewrite -hPsi -current_open_restriction_evaluation.
  apply:hZero.
  change (supportU psi `<=` W).
  rewrite -(@CurrentOpenRestrictionLocality.current_open_test_extension_support
    R h2 n m U V hU hV hUV psi) hPsi.
  by move=>z hz;exact:(hPhi z hz).1.
Qed.
End CurrentOpenRestrictionSupport.
