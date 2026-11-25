(** Federer (1969), 4.1.7, p. 359:
    properness on spt T makes
    the pullback of each compact target
    support localisable by one compact source
    cutoff. For a fixed target compact
    set the resulting map is continuous,
    and agrees with the actual pullback
    near the whole original current support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormClassZeroTopology NormOpenPreimage InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentProperSupport SmoothPullbackCutoffTests SmoothCompactSet SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothFormPullbackContinuity SmoothFormPullbackSupport SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothCutoffReplacement SmoothLocalAgreementSeminorm OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperPullbackTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m p:nat.
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
Variable T:@current_space R h2 v U hU p.
Local Notation support := (@current_support R h2 v U hU p T).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 v n p U hU V T f hImage.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).

(** Source for [current_proper_pullback_tests]:
    a fixed compact target support
    admits one continuous original E-to-D
    pullback replacement, supporting the definition
    of f#T in Federer 4.1.7,
    p. 359. The open agreement
    neighbourhood covers spt T, including
    the part outside the target support's
    inverse image. Global properness is unnecessary.
    The form degree m is independent
    of the degree p of T. *)
Theorem current_proper_pullback_tests (K:smooth_compact_set hNY V):
  exists Q:Hom E DT,
    open_family_continuous (smooth_function_opens hDE) (@current_test_opens R h2 v U hU m) Q /\
    exists W:set X,@open (real_norm_metric_space hNX) W /\support `<=` W /\W `<=` U /\
      forall phi:E,@smooth_function_support R Y B NY hNY V E ev phi `<=` smooth_compact_carrier K->
        forall x,W x->value (Q phi) x=fv (pull phi) x.
Proof.
pose L:=@current_proper_support_compact_locus R h2 v n p U hU V T f hImage hProper K.
apply:(@smooth_pullback_compact_locus_tests R h2 v n m U V hU hV support
  (fun x hx=>hx.1) f hImage hf K L).
move=>x hx hKx;exact:conj hx hKx.
Qed.
End CurrentProperPullbackTests.
