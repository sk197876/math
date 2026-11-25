(** Federer (1969), 4.1.7, p. 359:
    a compact inverse-support locus gives an
    actual continuous cutoff pullback near any
    prescribed carrier. This supporting form of
    the original construction also applies to
    f(spt T) in the composition proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormClassZeroTopology NormOpenPreimage InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothFormPullbackContinuity SmoothFormPullbackSupport SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothCutoffReplacement SmoothLocalAgreementSeminorm OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothPullbackCutoffTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation A := (A_m X R^o m).
Local Notation B := (A_m Y R^o m).
Local Notation PN := (@current_form_comass R h2 v m).
Local Notation hPN := (@current_form_comass_real_norm R h2 v m).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation DE := (@current_smooth_derivatives R h2 n V hV m).
Local Notation DF := (@current_smooth_derivatives R h2 v U hU m).
Local Notation hDE := (@current_smooth_derivative_laws R h2 n V hV m).
Local Notation hDF := (@current_smooth_derivative_laws R h2 v U hU m).
Local Notation DT := (@current_test_space R h2 v U hU m).
Local Notation value := (@current_test_value R h2 v U hU m).
Variable carrier:set X.
Hypothesis hCarrier:carrier `<=` U.
Arguments hCarrier : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).

(** Source for [smooth_pullback_compact_locus_tests]:
    one compact locus containing the inverse
    target support within the prescribed carrier
    gives a continuous original E-to-D pullback
    replacement near the whole carrier, supporting
    the defining cutoff and composition formulas
    in Federer 4.1.7, p. 359. *)
Theorem smooth_pullback_compact_locus_tests (K:smooth_compact_set hNY V)
    (L:smooth_compact_set hNX U):
  (forall x,carrier x->smooth_compact_carrier K (f x)->smooth_compact_carrier L x)->
  exists Q:Hom E DT,
    open_family_continuous (smooth_function_opens hDE) (@current_test_opens R h2 v U hU m) Q /\
    exists W:set X,@open (real_norm_metric_space hNX) W /\carrier `<=` W /\W `<=` U /\
      forall phi:E,@smooth_function_support R Y B NY hNY V E ev phi `<=` smooth_compact_carrier K->
        forall x,W x->value (Q phi) x=fv (pull phi) x.
Proof.
move=>hLocus.
pose replace:=@smooth_cutoff_replacement R X A NX PN hNX hPN v
  (@coordinate_basis R v) (@coordinate_basisP R v) U hU F fv hF L.
pose Q:=hom_comp replace pull.
have hPull:=@SmoothFormPullback.laws R h2 v n m U V hU hV f hImage hf.
have hPullC:=@smooth_form_pullback_continuous R h2 v n m U V hU hV f hImage hf pull hPull.
have hReplaceC:=@smooth_cutoff_replacement_continuous R X A NX PN hNX hPN v
  (@coordinate_basis R v) (@coordinate_basisP R v) U hU F fv hF DF hDF L.
have [W [hW [hLW [hWU hAgreement]]]]:=@smooth_cutoff_replacement_agrees_near_compact
  R X A NX PN hNX hPN v (@coordinate_basis R v) (@coordinate_basisP R v) U hU F fv hF L.
have hClosedK:@closed (real_norm_metric_space hNY) (smooth_compact_carrier K).
  exact:(compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) (smooth_compact_is_compact K)).
pose O:=fun x=>U x /\~smooth_compact_carrier K (f x).
have hO:@open (real_norm_metric_space hNX) O.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY U
    (~` smooth_compact_carrier K) f (norm_class_continuous (hf 0%N)) (closed_openC hClosedK)).
have hPullZero phi (hPhi:@smooth_function_support R Y B NY hNY V E ev phi `<=` smooth_compact_carrier K):
    forall x,O x->fv (pull phi) x=0.
  move=>x hx;exact:(@smooth_form_pullback_zero_off_compact R h2 v n m U V hU hV
    f hImage hf phi K hPhi x hx.1 hx.2).
exists Q;split;first exact:(open_family_continuous_compose hPullC hReplaceC).
exists (W `|` O);split;first exact:openU hW hO.
split.
- move=>x hx;case:(pselect (smooth_compact_carrier K (f x)))=>hKx.
  + left;exact:hLW x (hLocus x hx hKx).
  + right;exact:conj (hCarrier x hx) hKx.
- split;first by move=>x [hx|hx];[exact:hWU x hx|exact:hx.1].
  move=>phi hPhi x [hx|hx].
  + exact:hAgreement (pull phi) x hx.
  + have hZero:=hPullZero phi hPhi.
    have hAvoid:=@smooth_support_avoids_open_zero_set R X A NX hNX U F fv
      (pull phi) O hO hZero x hx.
    have hSupport:=@smooth_cutoff_replacement_support_subset R X A NX PN hNX hPN v
      (@coordinate_basis R v) (@coordinate_basisP R v) U hU F fv hF L (pull phi).
    have hValueZero:value (Q phi) x=0.
      apply:contrapT=>hNonzero;apply:hAvoid;apply:hSupport.
      split;first exact:hx.1.
      exact:(@subset_closure (real_norm_metric_space hNX) _ x hNonzero).
    by rewrite hValueZero (hZero x hx).
Qed.
End SmoothPullbackCutoffTests.
