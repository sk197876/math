(** Federer (1969), 4.1.7, p. 359:
    f#T(phi) is T applied to
    a compact cutoff of the original
    pullback. The independent action law below
    allows every actual compact test agreeing
    with that pullback near spt T.
    Properness supplies such tests separately;
    the action law assumes no existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentSpaces CurrentTestNearSupportAgreement SmoothFormPullbackSealed
  SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardUP.
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
Local Notation CT := (@current_space R h2 v U hU m).
Local Notation CS := (@current_space R h2 n V hV m).
Local Notation DU := (@current_test_space R h2 v U hU m).
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation value := (@current_test_value R h2 v U hU m).
Variable T:CT.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Let pb (phi:DV):=pull (smooth_test_inclusion hE phi).

(** Source for [is_current_pullback_test_replacement]:
    a genuine source test agrees
    with the original smooth pullback
    on an open neighbourhood of
    the whole current support, supporting
    the cutoff definition in Federer
    4.1.7, p. 359. *)
Definition is_current_pullback_test_replacement (phi:DV) (psi:DU):Prop:=
  exists W:set X,@open (real_norm_metric_space hNX) W /\
    @current_support R h2 v U hU m T `<=` W /\W `<=` U /\
    forall x,W x->value psi x=fv (pb phi) x.

(** Source for [is_current_pushforward]: every
    compact replacement of the original
    pullback gives the same defining
    current value, supporting f#T in
    Federer 4.1.7, p. 359.
    Construction and continuity are separate. *)
Definition is_current_pushforward (S:CS):Prop:=
  forall phi psi,is_current_pullback_test_replacement phi psi->
    @current_value R h2 n V hV m S phi=@current_value R h2 v U hU m T psi.

(** Source for [current_pullback_test_value_unique]:
    the defining value is independent
    of the chosen compact replacement,
    supporting Federer 4.1.7, p. 359,
    by the original current support theorem. *)
Lemma current_pullback_test_value_unique phi psi chi:
  is_current_pullback_test_replacement phi psi->is_current_pullback_test_replacement phi chi->
  @current_value R h2 v U hU m T psi=@current_value R h2 v U hU m T chi.
Proof.
move=>[W [hW [hTW [hWU hPsi]]]] [Z [hZ [hTZ [hZU hChi]]]].
apply:(@current_test_near_support_values_equal R h2 v m U hU T psi chi (W `&` Z)
  (openI hW hZ)).
- move=>x hx;exact:conj (hTW x hx) (hTZ x hx).
- move=>x hx;by rewrite (hPsi x hx.1) (hChi x hx.2).
Qed.

(** Source for [current_pullback_test_replacement_linear]:
    a common neighbourhood makes compact
    replacements respect every original linear
    combination, supporting linearity of the
    pushforward in Federer 4.1.7, p. 359.
    Only algebraic test operations are used. *)
Lemma current_pullback_test_replacement_linear c phi eta psi chi:
  is_current_pullback_test_replacement phi psi->is_current_pullback_test_replacement eta chi->
  is_current_pullback_test_replacement (c*:phi+eta) (c*:psi+chi).
Proof.
move=>[W [hW [hTW [hWU hPsi]]]] [Z [hZ [hTZ [hZU hChi]]]].
exists (W `&` Z);split;first exact:openI hW hZ.
split;first by move=>x hx;exact:conj (hTW x hx) (hTZ x hx).
split;first by move=>x hx;exact:hWU x hx.1.
move=>x hx.
have hSource:value (c*:psi+chi) x=c*:value psi x+value chi x.
  change (smooth_test_values_hom hF (c*:psi+chi) x=
    c*:smooth_test_values_hom hF psi x+smooth_test_values_hom hF chi x).
  by rewrite linearP.
have hTarget:fv (pb (c*:phi+eta)) x=c*:fv (pb phi) x+fv (pb eta) x.
  change (smooth_function_values_hom hF (pull (smooth_test_inclusion hE (c*:phi+eta))) x=
    c*:smooth_function_values_hom hF (pull (smooth_test_inclusion hE phi)) x+
      smooth_function_values_hom hF (pull (smooth_test_inclusion hE eta)) x).
  by rewrite !linearP.
rewrite hSource hTarget.
by rewrite (hPsi x hx.1) (hChi x hx.2).
Qed.
End CurrentPushforwardUP.
