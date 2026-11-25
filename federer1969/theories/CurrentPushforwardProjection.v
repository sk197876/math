(** Federer (1969), 4.1.7, p. 359:
    f#(T contracted with f#psi)=
    (f#T) contracted with psi for
    every original smooth form psi
    of admissible degree. A common
    compact source replacement and the
    original pullback product identity prove
    the actual current equality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentEvaluation
  CurrentContraction CurrentContractionSupport CurrentTestFormProduct SmoothCurrentFormProduct
  CurrentProperSupport CurrentProperSupportRestriction CurrentProperPullbackTests
  CurrentPushforwardUP CurrentPushforwardSealed SmoothFormPullbackSealed SmoothFormPullbackProduct
  SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPushforwardProjection.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k p:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable T:@current_space R h2 v U hU (k+p).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 v n (k+p) U hU V T f hImage.
Variable psi:@current_smooth_space R h2 n V hV k.
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n V hV d).
Local Notation fv := (fun d=>@current_smooth_value R h2 v U hU d).
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 v n d U V hU hV f hImage hf).
Local Notation C := (@current_contraction R h2 v k p U hU (pull k psi) T).

(** Source for [current_pushforward_smooth_contraction_proper]:
    the original source contraction has
    smaller support, so the printed
    properness hypothesis suffices for its
    pushforward, supporting Federer 4.1.7, p. 359. *)
Theorem current_pushforward_smooth_contraction_proper:
  @is_current_proper_on_support R h2 v n p U hU V C f hImage.
Proof.
exact:(@current_proper_smaller_support R h2 v n U hU V f hImage (k+p) p T C
  (@current_contraction_support_subset R h2 v k p U hU (pull k psi) T) hProper).
Qed.
Local Notation hCProper := current_pushforward_smooth_contraction_proper.

(** Source for [current_pushforward_smooth_projection]:
    the original smooth-form projection
    formula, Federer 4.1.7, p. 359.
    Encoding the current degree as
    k+p retains every admissible k,
    including both degree-zero endpoints.
    No integration representation or normality
    is imposed on the current. *)
Theorem current_pushforward_smooth_projection:
  @CurrentPushforward.value R h2 v n p U V hU hV C f hImage hf hCProper=
  @current_contraction R h2 n k p V hV psi
    (@CurrentPushforward.value R h2 v n (k+p) U V hU hV T f hImage hf hProper).
Proof.
apply:(@current_values_extensional R h2 n p V hV)=>eta.
have [K hK]:=smooth_test_support_bound (hE p) eta.
have [Q [hQC [W [hW [hTW [hWU hAgreement]]]]]]:=
  @current_proper_pullback_tests R h2 v n p (k+p) U V hU hV T f hImage hf hProper K.
pose alpha:=Q (smooth_test_inclusion (hE p) eta).
pose sourceProduct:=@current_test_form_product R h2 v k p U hU (pull k psi) alpha.
pose targetProduct:=@current_test_form_product R h2 n k p V hV psi eta.
have hAlpha x (hx:W x):@current_test_value R h2 v U hU p alpha x=
    fv p (pull p (smooth_test_inclusion (hE p) eta)) x.
  exact:hAgreement (smooth_test_inclusion (hE p) eta) hK x hx.
have hReplacementC:@is_current_pullback_test_replacement R h2 v n p U V hU hV C f hImage hf eta alpha.
  exists W;split;first exact:hW.
  split;first by move=>x hx;exact:hTW x (@current_contraction_support_subset R h2 v k p U hU (pull k psi) T x hx).
  split;[exact:hWU|exact:hAlpha].
have hInclusion:=congr1 (pull (k+p))
  (@current_test_form_product_inclusion R h2 n k p V hV psi eta).
have hPullProduct:=eq_trans hInclusion
  (@smooth_form_pullback_product R h2 v n k p U V hU hV f hImage hf
    psi (smooth_test_inclusion (hE p) eta)).
have hReplacementT:@is_current_pullback_test_replacement R h2 v n (k+p) U V hU hV T f hImage hf
    targetProduct sourceProduct.
  exists W;split;first exact:hW.
  split;first exact:hTW.
  split;first exact:hWU.
  move=>x hx.
  have hSource:=@current_test_form_product_values R h2 v k p U hU (pull k psi) alpha x (hWU x hx).
  rewrite (hAlpha x hx) in hSource.
  have hTarget:=congr1 (fun a=>fv (k+p) a x) hPullProduct.
  rewrite (@smooth_current_form_product_values R h2 v k p U hU (pull k psi)
    (pull p (smooth_test_inclusion (hE p) eta)) x (hWU x hx)) in hTarget.
  exact:(eq_trans hSource (esym hTarget)).
have hLeft:=eq_trans (@CurrentPushforward.laws R h2 v n p U V hU hV C f hImage hf hCProper
  eta alpha hReplacementC) (@current_contraction_evaluation R h2 v k p U hU (pull k psi) T alpha).
have hRight:=eq_trans (@current_contraction_evaluation R h2 n k p V hV psi
    (@CurrentPushforward.value R h2 v n (k+p) U V hU hV T f hImage hf hProper) eta)
  (@CurrentPushforward.laws R h2 v n (k+p) U V hU hV T f hImage hf hProper
    targetProduct sourceProduct hReplacementT).
exact:(eq_trans hLeft (esym hRight)).
Qed.
End CurrentPushforwardProjection.
