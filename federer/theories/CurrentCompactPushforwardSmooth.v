(** Federer (1969), 4.1.9, p. 363: compact currents
    in the point-current argument may be evaluated on original
    smooth forms after pushforward. Reuse the actual proper
    pushforward and unique smooth-dual extension of 4.1.7,
    pp. 355 and 359. No noncompact form is passed to D'. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentEvaluation CurrentProperSupport CurrentPushforwardUP CurrentPushforwardSealed CurrentPushforwardExistence
  CurrentPushforwardNormality CurrentCompactExtensionUP CurrentCompactExtensionSealed CurrentCompactSmoothValue
  CurrentCompactSmoothAgreement SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothDualRestriction ContinuousRealDual ContinuousRealDualTranspose
  SmoothFormPullbackSealed SmoothFormPullbackContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactPushforwardSmooth.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Variable T:@current_space R h2 v U hU m.
Hypothesis hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) (@current_support R h2 v U hU m T).
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hProper).
Local Notation hCompactS := (@current_pushforward_compact_support R h2 v n U V hU hV f hImage hf
  m T hProper hCompact).
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation hDE := (@current_smooth_derivative_laws R h2 n V hV m).
Local Notation hDF := (@current_smooth_derivative_laws R h2 v U hU m).
Local Notation OE := (smooth_function_opens hDE).
Local Notation OF := (smooth_function_opens hDF).
Local Notation hOE := (smooth_function_topology_laws hDE).1.
Local Notation hOF := (smooth_function_topology_laws hDF).1.
Local Notation Pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Local Notation hPull := (@smooth_form_pullback_continuous R h2 v n m U V hU hV f hImage hf Pull
  (@SmoothFormPullback.laws R h2 v n m U V hU hV f hImage hf)).
Local Notation LT := (@CompactCurrentExtension.value R h2 v m U hU T hCompact).
Local Notation LS := (@CompactCurrentExtension.value R h2 n m V hV S hCompactS).
Local Notation eE := (@continuous_real_dual_evaluation R E OE hOE).
Local Notation eF := (@continuous_real_dual_evaluation R F OF hOF).
Local Notation rho := (@current_smooth_dual_restriction R h2 n V hV m).

(** Source for [current_compact_pushforward_smooth_value]:
    the original extended pushforward satisfies f#T(phi)=T(f#phi)
    for every smooth phi when T has compact support, supporting
    the differential-form deduction in Federer 4.1.9, p. 363.
    Properness and compact support retain their actual meanings;
    the smooth dual, rather than the test dual, receives phi. *)
Theorem current_compact_pushforward_smooth_value (phi:E):
  @current_compact_smooth_value R h2 n m V hV S hCompactS phi=
    @current_compact_smooth_value R h2 v m U hU T hCompact (Pull phi).
Proof.
pose P:=@continuous_real_dual_transpose R E F OE OF hOE hOF Pull hPull.
have hRestriction:rho (P LT)=S.
  apply:(@current_values_extensional R h2 n m V hV)=>psi.
  have[alpha [W [hW [hTW [hWU hAgreement]]]]]:=
    @current_pushforward_test_replacement_exists R h2 v n m U V hU hV T f hImage hf hProper psi.
  have hReplacement:@is_current_pullback_test_replacement R h2 v n m U V hU hV T f hImage hf psi alpha.
    exists W;by split=>//;split=>//;split.
  have hValue:=@smooth_dual_test_restriction_evaluation R Y (A_m Y R^o m)
    NY (@current_form_comass R h2 n m) hNY (@current_form_comass_real_norm R h2 n m)
    V E ev hE (@current_smooth_derivatives R h2 n V hV m) hDE (P LT) psi.
  have hTranspose:=@continuous_real_dual_transpose_evaluation R E F OE OF hOE hOF
    Pull hPull LT (smooth_test_inclusion hE psi).
  have hTest:=@current_compact_near_support_smooth_value R h2 v m U hU T hCompact
    (Pull (smooth_test_inclusion hE psi)) alpha W hW hTW (fun x hx=>esym (@hAgreement x hx)).
  exact:(eq_trans hValue (eq_trans hTranspose (eq_trans hTest
    (esym (@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hProper psi alpha hReplacement))))).
have hEqual:LS=(P LT:@current_smooth_dual_space R h2 n V hV m).
  apply:(@current_compact_extension_unique R h2 n m V hV S).
  - exact:(@CompactCurrentExtension.laws R h2 n m V hV S hCompactS).
  - exact:hRestriction.
change (eE LS phi=eF LT (Pull phi));rewrite hEqual.
exact:(@continuous_real_dual_transpose_evaluation R E F OE OF hOE hOF Pull hPull LT phi).
Qed.
End CurrentCompactPushforwardSmooth.
