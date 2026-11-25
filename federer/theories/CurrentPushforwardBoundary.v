(** Federer (1969), 4.1.7, p. 359:
    boundary(f#T)=f#(boundary T) for the
    original proper pushforward. One compact
    replacement agrees with the pullback
    near spt T, so its
    actual derivative agrees there too.
    The original 4.1.6 pullback differential
    law and boundary evaluations give the result. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces
  CurrentEvaluation CurrentBoundary CurrentBoundarySupport CurrentProperSupport CurrentProperSupportRestriction
  CurrentProperPullbackTests CurrentPushforwardUP CurrentPushforwardSealed
  SmoothFormPullbackSealed SmoothFormPullbackDifferential SmoothCurrentExteriorDerivative
  CurrentTestExteriorDerivative CurrentTestExteriorAgreement SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPushforwardBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
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
Variable T:@current_space R h2 v U hU m.+1.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 v n m.+1 U hU V T f hImage.
Local Notation bd := (@current_boundary R h2 v m U hU T).

(** Source for [current_pushforward_boundary_proper]:
    properness on spt T implies
    properness on spt(boundary T), supporting
    the actual right side of
    the boundary equation in Federer
    4.1.7, p. 359. The
    support inclusion and relative closedness
    are proved beforehand. *)
Theorem current_pushforward_boundary_proper:
  @is_current_proper_on_support R h2 v n m U hU V bd f hImage.
Proof.
exact:(@current_proper_smaller_support R h2 v n U hU V f hImage m.+1 m T bd
  (@current_boundary_support_subset R h2 v m U hU T) hProper).
Qed.
Local Notation hBoundaryProper := current_pushforward_boundary_proper.
Local Notation S := (@CurrentPushforward.value R h2 v n m.+1 U V hU hV T f hImage hf hProper).
Local Notation B := (@CurrentPushforward.value R h2 v n m U V hU hV bd f hImage hf hBoundaryProper).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 n V hV k).
Local Notation sv := (fun k=>@current_smooth_value R h2 v U hU k).
Local Notation pull := (fun k=>@SmoothFormPullback.operator R h2 v n k U V hU hV f hImage hf).
Local Notation dV := (@current_test_exterior_derivative R h2 n m V hV).
Local Notation dU := (@current_test_exterior_derivative R h2 v m U hU).

(** Source for [current_pushforward_boundary]:
    boundary(f#T)=f#(boundary T), Federer
    4.1.7, p. 359. This
    holds for every original positive-degree
    current whose support restriction is
    proper; no representation, finite mass
    or normality is assumed. *)
Theorem current_pushforward_boundary:
  @current_boundary R h2 n m V hV S=B.
Proof.
apply:(@current_values_extensional R h2 n m V hV)=>phi.
have [K hK]:=smooth_test_support_bound (hE m) phi.
have [Q [hQC [W [hW [hTW [hWU hAgreement]]]]]]:=
  @current_proper_pullback_tests R h2 v n m m.+1 U V hU hV T f hImage hf hProper K.
pose psi:=Q (smooth_test_inclusion (hE m) phi).
have hValue x (hx:W x):@current_test_value R h2 v U hU m psi x=
    sv m (pull m (smooth_test_inclusion (hE m) phi)) x.
  exact:hAgreement (smooth_test_inclusion (hE m) phi) hK x hx.
have hBoundaryReplacement:@is_current_pullback_test_replacement R h2 v n m U V hU hV bd f hImage hf phi psi.
  exists W;split;first exact:hW.
  split;first by move=>x hx;exact:hTW x (@current_boundary_support_subset R h2 v m U hU T x hx).
  split;[exact:hWU|exact:hValue].
have hCommuted:=@smooth_form_pullback_exterior_commutes R h2 v n m U V hU hV f hImage hf
  (smooth_test_inclusion (hE m) phi).
have hInclusion:=congr1 (pull m.+1)
  (@current_test_exterior_derivative_inclusion R h2 n m V hV phi).
have hDerivative:@smooth_current_exterior_derivative R h2 v m U hU
    (pull m (smooth_test_inclusion (hE m) phi))=
    pull m.+1 (smooth_test_inclusion (hE m.+1) (dV phi)).
  exact:(eq_trans hCommuted (esym hInclusion)).
have hCurrentReplacement:@is_current_pullback_test_replacement R h2 v n m.+1 U V hU hV T f hImage hf
    (dV phi) (dU psi).
  exists W;split;first exact:hW.
  split;first exact:hTW.
  split;first exact:hWU.
  move=>x hx.
  have hLocal:=@current_test_exterior_local_agreement R h2 v m U hU psi
    (pull m (smooth_test_inclusion (hE m) phi)) W hW hWU hValue x hx.
  exact:(eq_trans hLocal (congr1 (fun a=>sv m.+1 a x) hDerivative)).
have hLeft:=eq_trans (@current_boundary_evaluation R h2 n m V hV S phi)
  (@CurrentPushforward.laws R h2 v n m.+1 U V hU hV T f hImage hf hProper
    (dV phi) (dU psi) hCurrentReplacement).
have hRight:=eq_trans (@CurrentPushforward.laws R h2 v n m U V hU hV bd f hImage hf hBoundaryProper
    phi psi hBoundaryReplacement) (@current_boundary_evaluation R h2 v m U hU T psi).
exact:(eq_trans hLeft (esym hRight)).
Qed.
End CurrentPushforwardBoundary.
