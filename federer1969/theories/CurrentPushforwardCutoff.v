(** Federer (1969), 4.1.7, p. 359:
    the original equation f#T(phi)=T(gamma
    wedge f#phi) holds for every
    gamma in D^0(U) equal to
    one on a neighbourhood of
    spt T intersect f inverse(spt phi).
    The source test below uses exactly
    the original product and equal-degree transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormRegularity NormOpenPreimage InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingProduct
  ScalarCoefficients ExteriorHomogeneousProducts CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry
  CurrentDegreeTransport CurrentTestFormProduct CurrentScalarFormProduct CurrentProperSupport
  SmoothFormPullbackUP SmoothFormPullbackSealed SmoothFormPullbackSupport CurrentPushforwardUP CurrentPushforwardSealed
  SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardCutoff.
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
Local Notation D0 := (@current_test_space R h2 v U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation value := (@current_test_value R h2 v U hU m).
Local Notation scalar := (@current_test_value R h2 v U hU 0%N).
Variable T:@current_space R h2 v U hU m.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Let pb (phi:DV):=pull (smooth_test_inclusion hE phi).

(** Source for [current_pushforward_cutoff_test]:
    gamma wedge f#phi is an
    actual compact source test in
    the original defining equation, Federer
    4.1.7, p. 359. The
    scalar right factor agrees with
    the printed degree-zero left factor. *)
Definition current_pushforward_cutoff_test (phi:DV) (gamma:D0):DU:=
  @current_test_degree_transport R h2 v U hU (m+0)%N m (addn0 m)
    (@current_test_form_product R h2 v m 0%N U hU (pb phi) gamma).

(** Source for [current_pushforward_cutoff_test_values]:
    the original compact cutoff test
    has value gamma(x) times f#phi(x),
    supporting Federer 4.1.7, p. 359. *)
Lemma current_pushforward_cutoff_test_values phi gamma x:U x->
  value (current_pushforward_cutoff_test phi gamma) x=
    (zero_form_value (scalar gamma x):R)*:fv (pb phi) x.
Proof.
move=>hx.
have hTransport:=@current_test_degree_transport_values R h2 v U hU (m+0)%N m (addn0 m)
  (@current_test_form_product R h2 v m 0%N U hU (pb phi) gamma) x.
rewrite (@current_test_form_product_values R h2 v m 0%N U hU (pb phi) gamma x hx) in hTransport.
have hScalar:form_reindex (addn0 m)
    (form_wedge h2 (scalar_bilinear R) (fv (pb phi) x) (scalar gamma x))=
    (zero_form_value (scalar gamma x):R)*:fv (pb phi) x.
  rewrite -{1}(zero_form_valueK (scalar gamma x)).
  exact:current_form_wedge_zero_scalar.
exact:(eq_trans hTransport hScalar).
Qed.

(** Source for [current_pushforward_cutoff_replacement]:
    every printed admissible gamma gives
    a genuine compact replacement near
    the whole original current support,
    supporting Federer 4.1.7, p. 359.
    The plateau is required only
    over spt T intersect f inverse(spt phi). *)
Theorem current_pushforward_cutoff_replacement (phi:DV) (gamma:D0):
  (forall x,@current_support R h2 v U hU m T x->
    @current_test_support R h2 n m V hV phi (f x)->
    @interior (real_norm_metric_space hNX) [set z|scalar gamma z=@zero_form R X R^o 1] x)->
  @is_current_pullback_test_replacement R h2 v n m U V hU hV T f hImage hf phi
    (current_pushforward_cutoff_test phi gamma).
Proof.
move=>hPlateau.
pose K:=@Build_smooth_compact_set R Y NY hNY V
  (@current_test_support R h2 n m V hV phi) (fun y hy=>hy.1)
  (smooth_test_support_compact hE phi).
have hClosedK:@closed (real_norm_metric_space hNY) (smooth_compact_carrier K).
  exact:(compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) (smooth_compact_is_compact K)).
pose O:=fun x=>U x /\~smooth_compact_carrier K (f x).
have hO:@open (real_norm_metric_space hNX) O.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY U
    (~` smooth_compact_carrier K) f (norm_class_continuous (hf 0%N)) (closed_openC hClosedK)).
have hOpenU:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
pose W:=(@interior (real_norm_metric_space hNX)
  [set z|scalar gamma z=@zero_form R X R^o 1]) `&` U.
have hW:@open (real_norm_metric_space hNX) W:=
  openI (@open_interior (real_norm_metric_space hNX)
    [set z|scalar gamma z=@zero_form R X R^o 1]) hOpenU.
have hOff x (hx:O x):fv (pb phi) x=0.
  exact:(@smooth_form_pullback_zero_off_compact R h2 v n m U V hU hV
    f hImage hf (smooth_test_inclusion hE phi) K (fun y hy=>hy) x hx.1 hx.2).
exists (W `|` O);split;first exact:openU hW hO.
split.
- move=>x hx;case:(pselect (smooth_compact_carrier K (f x)))=>hKx.
  + left;exact:conj (hPlateau x hx hKx) hx.1.
  + right;exact:conj hx.1 hKx.
- split;first by move=>x [hx|hx];[exact:hx.2|exact:hx.1].
  move=>x [hx|hx].
  + rewrite (current_pushforward_cutoff_test_values phi gamma hx.2).
    have hOne:scalar gamma x=@zero_form R X R^o 1:=interior_subset hx.1.
    by rewrite hOne zero_formK scale1r.
  + by rewrite (current_pushforward_cutoff_test_values phi gamma hx.1) (hOff x hx) scaler0.
Qed.

(** Source for [current_pushforward_original_cutoff_formula]:
    the literal original defining equation
    for every admissible gamma in
    D^0(U), Federer 4.1.7, p. 359.
    Properness of f on spt T
    is exactly the printed hypothesis. *)
Theorem current_pushforward_original_cutoff_formula
    (hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage) phi gamma:
  (forall x,@current_support R h2 v U hU m T x->
    @current_test_support R h2 n m V hV phi (f x)->
    @interior (real_norm_metric_space hNX) [set z|scalar gamma z=@zero_form R X R^o 1] x)->
  @current_value R h2 n V hV m
    (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hProper) phi=
  @current_value R h2 v U hU m T (current_pushforward_cutoff_test phi gamma).
Proof.
move=>hPlateau.
exact:(@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hProper
  phi (current_pushforward_cutoff_test phi gamma) (current_pushforward_cutoff_replacement hPlateau)).
Qed.
End CurrentPushforwardCutoff.
