(** Federer (1969), 4.1.14, p. 371: the
    original locally flat image has support in f(spt T).
    The all-cutoff equation and the preceding compact
    support theorem prove annihilation away from that
    image. Properness only on spt T makes its
    image relatively closed, as in 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  OpenLocalLipschitzCompact SmoothCompactSet CurrentSpaces
  CurrentSupportGeometry CurrentSupportAgreement CurrentSupportMapTopology
  CurrentProperSupport CurrentContraction CurrentContractionSupport
  SmoothTestSpaces SmoothTestEvaluation FlatCurrentsUP CurrentLipschitzPushforwardUP
  CurrentLipschitzCutoffExistence CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImageSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hQ:@is_current_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal T Q.
Local Notation support:=(@current_support R h2 n U hU m T).
Local Notation targetSupport:=(@current_test_support R h2 nu m V hV).

(** Source for [current_lipschitz_image_test_away_from_image]:
    every original target test away from f(spt T)
    has zero image action, supporting Federer 4.1.14,
    p. 371. No nonsmooth pullback is evaluated. *)
Lemma current_lipschitz_image_test_away_from_image
    (phi:@current_test_space R h2 nu V hV m):
  (forall x,support x->~targetSupport phi (f x))->
  @current_value R h2 nu V hV m Q phi=0.
Proof.
move=>hAvoid.
have[K hK]:=smooth_test_support_bound (@current_smooth_space_laws R h2 nu V hV m) phi.
have[gamma hGamma]:=@current_lipschitz_compact_target_cutoff R h2 n nu m
  U V hU hV T f hImage hProper K.
pose S:=@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T.
pose hS:=hT gamma.
rewrite (hQ.2 phi gamma hS (hGamma phi hK)).
apply:(@current_test_disjoint_support_zero R h2 nu m V hV).
move=>y hy hPhi.
have[x hx hFx]:=@current_flat_lipschitz_pushforward_support R h2 n nu m
  U V hU hV f hImage hLocal S hS y hy.
have hxT:support x:=@current_contraction_support_subset R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T x hx.
apply:(hAvoid x hxT);by rewrite hFx.
Qed.

(** Source for [current_lipschitz_image_support]:
    spt(f#T) is contained in f(spt T),
    Federer 4.1.14, p. 371. Original support
    properness suffices; no global properness is added. *)
Theorem current_lipschitz_image_support:
  @current_support R h2 nu V hV m Q `<=` f @` support.
Proof.
move=>y [hy hSupport];apply:contrapT=>hNotImage.
pose O:=[set z|V z /\~exists x,support x /\f x=z].
have hf:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hLocal.
have hO:@open (real_norm_metric_space hNY) O.
  exact:(@current_proper_support_image_complement_open R h2 n nu m U hU
    V hV T f hImage hf hProper).
apply:hSupport;exists O;split.
- split;first exact:hO.
  move=>phi hPhi;apply:current_lipschitz_image_test_away_from_image=>x hx hPhiX.
  have hNo:~exists z,support z /\f z=f x:=(hPhi (f x) hPhiX).2.
  apply:hNo;exists x;by split.
- split;first exact:hy.
  move=>[x [hx hFx]];apply:hNotImage;by exists x.
Qed.
End CurrentLipschitzImageSupport.
