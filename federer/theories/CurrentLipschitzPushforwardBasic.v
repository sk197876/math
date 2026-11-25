(** Federer (1969), 4.1.14, p. 371: public
    laws of the original locally flat Lipschitz image.
    Derive them from its independent all-cutoff
    specification and previously proved candidate laws.
    Every cutoff and gluing choice remains behind
    the opaque image interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentSupportGeometry CurrentProperSupport
  FlatCurrentsUP FlatCurrentUnion CurrentLipschitzPushforwardUP
  CurrentLipschitzPushforwardSealed CurrentLipschitzImageUniqueness
  CurrentLipschitzImageCompactAgreement CurrentLipschitzImageLinear
  CurrentLipschitzImageSupport CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzPushforwardBasic.
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
Local Notation CU:=(@current_space R h2 n U hU m).
Local Notation LocalFlat:=(@is_locally_flat_current R h2 n m U hU).
Local Notation Proper:=(fun T:CU=>@is_current_proper_on_support R h2 n nu m U hU V T f hImage).
Local Notation Push:=(@CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal).
Local Notation Laws:=(@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hImage hLocal).

(** Source for [current_lipschitz_pushforward_proof_independent]:
    the original actual image is independent of
    the evidence of local flatness and support
    properness, supporting Federer 4.1.14, p. 371. *)
Lemma current_lipschitz_pushforward_proof_independent
    (T:CU) (hT hT':LocalFlat T) (hProper hProper':Proper T):
  Push T hT hProper=Push T hT' hProper'.
Proof.
exact:(@current_lipschitz_image_unique R h2 n nu m U V hU hV
  f hImage hLocal T hT hProper _ _ (Laws T hT hProper) (Laws T hT' hProper')).
Qed.

(** Source for [current_lipschitz_pushforward_congruence]:
    equal original locally flat currents have
    equal actual images, supporting the homotopy
    identities in Federer 4.1.14, p. 371. *)
Lemma current_lipschitz_pushforward_congruence
    (T S:CU) (hT:LocalFlat T) (hS:LocalFlat S)
    (hProperT:Proper T) (hProperS:Proper S):
  T=S->Push T hT hProperT=Push S hS hProperS.
Proof.
move=>hEquality;subst S.
exact:current_lipschitz_pushforward_proof_independent.
Qed.

(** Source for [current_lipschitz_pushforward_data_independent]:
    the original actual image does not depend
    on evidence of its image, regularity, local
    flatness or support properness, supporting
    Federer 4.1.14, p. 371. *)
Lemma current_lipschitz_pushforward_data_independent
    (hImage':forall x,U x->V (f x))
    (hLocal':@is_locally_metric_lipschitz R
      (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
    (T:CU) (hT hT':LocalFlat T) (hProper:Proper T)
    (hProper':@is_current_proper_on_support R h2 n nu m U hU V T f hImage'):
  Push T hT hProper=
    @CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
      f hImage' hLocal' T hT' hProper'.
Proof.
have hImageEquality:hImage'=hImage:=Prop_irrelevance _ _;subst hImage'.
have hLocalEquality:hLocal'=hLocal:=Prop_irrelevance _ _;subst hLocal'.
exact:current_lipschitz_pushforward_proof_independent.
Qed.

(** Source for [current_lipschitz_pushforward_compact]:
    the original local image agrees with the
    compact flat definition, Federer 4.1.14, p. 371. *)
Theorem current_lipschitz_pushforward_compact
    (T:CU) (hT:LocalFlat T) (hProper:Proper T)
    (hFlat:@is_flat_current R h2 n m U hU T):
  Push T hT hProper=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal T hFlat.
Proof.
exact:(@current_lipschitz_image_compact_agreement R h2 n nu m U V hU hV
  f hImage hLocal T hFlat _ (Laws T hT hProper)).
Qed.

(** Source for [current_lipschitz_pushforward_linear]:
    f#(cT+S)=c f#T+f#S for original locally
    flat currents, Federer 4.1.14, p. 371.
    Properness of the combination may be supplied
    by the preceding support-union law; its evidence
    does not affect the image. *)
Theorem current_lipschitz_pushforward_linear c (T S:CU)
    (hT:LocalFlat T) (hS:LocalFlat S)
    (hProperT:Proper T) (hProperS:Proper S)
    (hProperC:Proper (c*:T+S)):
  Push (c*:T+S) (@locally_flat_current_linear_combination R h2 n m U hU
    c T S hT hS) hProperC=c*:Push T hT hProperT+Push S hS hProperS.
Proof.
exact:(@current_lipschitz_image_linear R h2 n nu m U V hU hV
  f hImage hLocal c T S _ _ _ hT hS hProperT hProperS
  (Laws T hT hProperT) (Laws S hS hProperS)
  (Laws (c*:T+S) (@locally_flat_current_linear_combination R h2 n m U hU
    c T S hT hS) hProperC)).
Qed.

(** Source for [current_lipschitz_pushforward_support]:
    spt(f#T) is contained in f(spt T),
    Federer 4.1.14, p. 371, under only
    the original support-properness condition. *)
Theorem current_lipschitz_pushforward_support (T:CU)
    (hT:LocalFlat T) (hProper:Proper T):
  @current_support R h2 nu V hV m (Push T hT hProper) `<=`
    f @` @current_support R h2 n U hU m T.
Proof.
exact:(@current_lipschitz_image_support R h2 n nu m U V hU hV
  f hImage hLocal T hT hProper _ (Laws T hT hProper)).
Qed.
End CurrentLipschitzPushforwardBasic.
