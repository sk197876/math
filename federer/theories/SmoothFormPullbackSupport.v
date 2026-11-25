(** Federer (1969), 4.1.7, p. 359:
    a pullback vanishes away from
    the inverse image of the
    original target support. This supporting
    locality law connects the actual
    4.1.6 pullback to the compact
    cutoff and current support arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormOpenPreimage InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingDual CurrentCoefficientNorms CurrentSpaces SmoothCompactSet SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothFunctionSupport SmoothLocalAgreementSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothFormPullbackSupport.
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
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).

(** Source for [smooth_form_pullback_zero_off_compact]:
    a form supported in K
    pulls back to zero at
    every original domain point outside
    f inverse(K), supporting the defining
    cutoff formula in Federer 4.1.7,
    p. 359. No properness assumption
    is needed for this pointwise law. *)
Theorem smooth_form_pullback_zero_off_compact (phi:E) (K:smooth_compact_set hNY V):
  @smooth_function_support R Y B NY hNY V E ev phi `<=` smooth_compact_carrier K->
  forall x,U x->~smooth_compact_carrier K (f x)->fv (pull phi) x=0.
Proof.
move=>hPhi x hx hOff.
have [D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 (hf 1%N).
have hZero:=(@smooth_function_compact_support_iff R Y B NY
  (@current_form_comass R h2 n m) hNY (@current_form_comass_real_norm R h2 n m)
  V E ev hE K phi).1 hPhi (f x) hOff.
rewrite (@smooth_form_pullback_values R v n m U V E F ev fv f pull
  (@SmoothFormPullback.laws R h2 v n m U V hU hV f hImage hf) phi x (D x) hx
  (norm_class_one_differential hD hx)) hZero;exact:linear0.
Qed.

(** Source for [smooth_form_pullback_support_preimage]:
    the actual smooth pullback support
    lies in U intersect f inverse(K),
    supporting the proper pushforward cutoff
    in Federer 4.1.7, p. 359.
    Closedness of compact K and
    continuity of f give the
    required open zero neighbourhoods. *)
Theorem smooth_form_pullback_support_preimage (phi:E) (K:smooth_compact_set hNY V):
  @smooth_function_support R Y B NY hNY V E ev phi `<=` smooth_compact_carrier K->
  @smooth_function_support R X A NX hNX U F fv (pull phi) `<=`
    [set x|U x /\smooth_compact_carrier K (f x)].
Proof.
move=>hPhi x hx;split;first exact:hx.1.
apply:contrapT=>hOff.
pose O:=fun z=>U z /\~smooth_compact_carrier K (f z).
have hClosedK:@closed (real_norm_metric_space hNY) (smooth_compact_carrier K).
  exact:(compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) (smooth_compact_is_compact K)).
have hO:@open (real_norm_metric_space hNX) O.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY U
    (~` smooth_compact_carrier K) f (norm_class_continuous (hf 0%N)) (closed_openC hClosedK)).
have hZero z (hz:O z):fv (pull phi) z=0.
  exact:(smooth_form_pullback_zero_off_compact hPhi hz.1 hz.2).
exact:(@smooth_support_avoids_open_zero_set R X A NX hNX U F fv
  (pull phi) O hO hZero x (conj hx.1 hOff) hx).
Qed.
End SmoothFormPullbackSupport.
