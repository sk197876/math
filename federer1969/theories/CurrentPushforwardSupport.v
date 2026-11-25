(** Federer (1969), 4.1.7, p. 359:
    spt(f#T) is contained in f(spt T).
    Properness makes the support image
    relatively closed; tests supported in
    its open complement have zero
    pullback near the whole source support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormOpenPreimage InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry CurrentSupportMapTopology
  CurrentProperSupport SmoothFormPullbackUP SmoothFormPullbackSealed SmoothFormPullbackSupport CurrentPushforwardUP
  CurrentPushforwardSealed SmoothCompactSet SmoothFunctionSpaceLaws SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardSupport.
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
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation DU := (@current_test_space R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation value := (@current_test_value R h2 v U hU m).
Variable T:@current_space R h2 v U hU m.
Local Notation support := (@current_support R h2 v U hU m T).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hProper).
Local Notation targetSupport := (@current_test_support R h2 n m V hV).

(** Source for [current_pushforward_test_away_from_image]:
    a compact target test whose
    support avoids f(spt T) has
    zero pushforward value, supporting the
    support-image inclusion in Federer 4.1.7,
    p. 359. Its actual pullback
    vanishes on an open neighbourhood
    of the whole source support. *)
Lemma current_pushforward_test_away_from_image (phi:DV):
  (forall x,support x->~targetSupport phi (f x))->
  @current_value R h2 n V hV m S phi=0.
Proof.
move=>hAvoid.
pose K:=@Build_smooth_compact_set R Y NY hNY V
  (targetSupport phi) (fun y hy=>hy.1) (smooth_test_support_compact hE phi).
have hClosedK:@closed (real_norm_metric_space hNY) (smooth_compact_carrier K).
  exact:(compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) (smooth_compact_is_compact K)).
pose O:=fun x=>U x /\~smooth_compact_carrier K (f x).
have hO:@open (real_norm_metric_space hNX) O.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY U
    (~` smooth_compact_carrier K) f (norm_class_continuous (hf 0%N)) (closed_openC hClosedK)).
have hZero x (hx:O x):fv (pull (smooth_test_inclusion hE phi)) x=0.
  exact:(@smooth_form_pullback_zero_off_compact R h2 v n m U V hU hV
    f hImage hf (smooth_test_inclusion hE phi) K (fun y hy=>hy) x hx.1 hx.2).
have hReplacement:@is_current_pullback_test_replacement R h2 v n m U V hU hV T f hImage hf phi (0:DU).
  exists O;split;first exact:hO.
  split;first by move=>x hx;exact:conj hx.1 (hAvoid x hx).
  split;first by move=>x hx;exact:hx.1.
  move=>x hx;change (smooth_test_values_hom hF 0 x=fv (pull (smooth_test_inclusion hE phi)) x).
  by rewrite linear0 /= (hZero x hx).
have hValue:=@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hProper phi 0 hReplacement.
by rewrite hValue linear0.
Qed.

(** Source for [current_pushforward_support_image]:
    spt(f#T) is contained in
    f(spt T), Federer 4.1.7,
    p. 359. The original properness
    on spt T gives the
    open complement needed in the
    actual functional-support definition. *)
Theorem current_pushforward_support_image:
  @current_support R h2 n V hV m S `<=` f @` support.
Proof.
move=>y [hy hSupport];apply:contrapT=>hNotImage.
pose W:=[set z|V z /\~exists x,support x /\f x=z].
have hW:@open (real_norm_metric_space hNY) W.
  exact:(@current_proper_support_image_complement_open R h2 v n m U hU V hV T f hImage
    (norm_class_continuous (hf 0%N)) hProper).
apply:hSupport;exists W;split.
- split;first exact:hW.
  move=>phi hPhi;apply:current_pushforward_test_away_from_image=>x hx hPhiX.
  have hNo:~exists z,support z /\f z=f x:=(hPhi (f x) hPhiX).2.
  apply:hNo;exists x;by split.
- split;first exact:hy.
  move=>[x [hx hFx]];apply:hNotImage;by exists x.
Qed.
End CurrentPushforwardSupport.
