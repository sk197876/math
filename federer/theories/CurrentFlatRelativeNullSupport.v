(** Federer (1969), 4.1.21, p. 378: if
    the part of a flat positive-degree support
    outside B is relatively closed, and
    B meets the support in an
    integral-geometric null set, then the support
    avoids B. Follow the printed compact
    scalar cutoff proof and the preceding
    null-support theorem. Use the preceding null-support theorem of 4.1.20. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormOpenTopology NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero
  SmoothCompactSet SmoothTestSpaces CurrentSpaces CurrentSupportGeometry
  CurrentContraction CurrentContractionSupport CurrentTestContractionSupport
  CurrentScalarPlateau CurrentTestFormProduct CurrentEvaluation
  CurrentSupportAgreement CurrentNeighbourhoodCutoff FlatCurrentsUP FlatCurrentScalarClosure
  IntegralGeometricMeasure MeasureUP MeasureAlmostBasic CurrentFlatIntegralGeometricNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatRelativeNullSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Variable U:set (R_n R n).
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable T:@current_space R h2 n U hU m.
Local Notation support:=(@current_support R h2 n U hU m T).
Local Notation IG:=(@integral_geometric_measure R n m hMN 1%E).

(** Source for [current_flat_relative_integral_geometric_null]:
    the complete first corollary of 4.1.21,
    p. 378. B is an arbitrary
    original subset of U. Only support
    minus B is closed in the
    relative topology of U; B itself
    need not be open, closed or
    measurable. No mass, representation or
    normality premise is imposed on T. *)
Theorem current_flat_relative_integral_geometric_null (B:set X):
  (0<m)%N->@is_flat_current R h2 n m U hU T->B `<=` U->
  @closed (subspace (U:set XT)) (support `\` B)->
  IG (B `&` support)=0%E->support `<=` (U `\` B).
Proof.
move=>hPositive hFlat hBU hRelative hNull x hx;split;first exact:hx.1.
move=>hxB.
have[F hClosed hEquation]:=(@closed_subspaceP XT U (support `\` B)).1 hRelative.
have hOpenU:@open XT U.
  rewrite openE=>y hy;exact:(@norm_domain_interior_neighbourhood R X NX hNX U y).1
    (hU y hy).
pose W:set X:=U `\` F.
have hOpenW:@open XT W:=openI hOpenU (closed_openC hClosed).
have hxNotF:~F x.
  move=>hxF;have hBad:((support `\` B) `&` U) x.
    rewrite -hEquation;exact:conj hxF hx.1.
  exact:hBad.1.2 hxB.
pose K:=@smooth_compact_singleton R X NX hNX U x (hBU x hxB).
have hKW:smooth_compact_carrier K `<=` W.
  move=>y hy;change (y=x) in hy;subst y;exact:conj (hBU x hxB) hxNotF.
have[gamma [hGamma [V [hV [hKV [hVW hOne]]]]]]:=
  @current_neighbourhood_scalar_cutoff R h2 n U hU K W hOpenW hKW (fun y hy=>hy.1).
pose g:=smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma.
pose Q:=@current_contraction R h2 n 0%N m U hU g T.
have hQFlat:=@flat_current_scalar_multiplier R h2 n m U hU gamma T hFlat.
have hQSupport:@current_support R h2 n U hU m Q `<=` (B `&` support).
  move=>y hy.
  have hyT:=@current_contraction_support_subset R h2 n 0%N m U hU g T y hy.
  have hyGamma:=@current_contraction_test_support_subset R h2 n 0%N m U hU gamma T y hy.
  have hyW:=hGamma y hyGamma.
  split;last exact:hyT.
  apply:contrapT=>hyNotB.
  have hBad:((support `\` B) `&` U) y:=conj (conj hyT hyNotB) hyT.1.
  have hIn:(F `&` U) y by rewrite hEquation;exact:hBad.
  exact:hyW.2 hIn.1.
have hQNull:IG (@current_support R h2 n U hU m Q)=0%E.
  exact:(measure_null_subset
    (@integral_geometric_measure_is_measure R n m hMN 1%E (lexx _)) hQSupport hNull).
have hQZero:=@current_flat_integral_geometric_null R h2 n m hMN U hU Q
  hPositive hQFlat hQNull.
have hDifference:=@current_support_difference_agreement R h2 n m U hU T Q V hV.
have hAgreement:forall psi:@current_test_space R h2 n U hU m,
    @current_test_support R h2 n m U hU psi `<=` V->
    @current_value R h2 n U hU m T psi=@current_value R h2 n U hU m Q psi.
  move=>psi hPsi;rewrite current_contraction_evaluation.
  by rewrite (@current_scalar_test_local_plateau R h2 n m U hU V g hOne psi hPsi).
have hxV:V x:=hKV x (erefl x).
have hDiffSupport:=hDifference hAgreement.
have hDifferenceCurrent:T-Q=T by rewrite hQZero subr0.
have hAt:@current_support R h2 n U hU m (T-Q) x by rewrite hDifferenceCurrent.
exact:(hDiffSupport x hAt).2 hxV.
Qed.
End CurrentFlatRelativeNullSupport.
