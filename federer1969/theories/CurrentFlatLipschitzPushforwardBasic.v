(** Federer (1969), 4.1.14, p. 371: the
    original union image is linear, preserves normality
    and has support in f(spt T). Prove these laws
    through the independent compact-index specifications;
    the sealed index choice is never inspected. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  NormalCurrentsUP FlatCurrentsUP FlatCurrentClosure FlatCurrentUnion FlatCurrentFinite
  CurrentFlatCompactMonotone CurrentCompactLipschitzImageLinear
  CurrentCompactLipschitzImageUniqueness CurrentCompactLipschitzImageSupport
  CurrentNormalLipschitzImageExistence CurrentFlatLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardExistence CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatLipschitzPushforwardBasic.
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
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Flat:=(@is_flat_current R h2 n m U hU).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal).
Local Notation Laws:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hImage hLocal).

(** Source for [current_flat_lipschitz_pushforward_proof_independent]:
    the actual image depends on T rather than its
    membership evidence, supporting Federer 4.1.14, p. 371. *)
Lemma current_flat_lipschitz_pushforward_proof_independent
    (T:C) (hT hT':Flat T):Push T hT=Push T hT'.
Proof.
exact:(@current_flat_lipschitz_pushforward_unique R h2 n nu m U V hU hV
  f hImage hLocal T hT _ _ (Laws T hT) (Laws T hT')).
Qed.

(** Source for [current_flat_lipschitz_pushforward_linear]:
    f#(cT+S)=c f#T+f#S on the original union,
    Federer 4.1.14, p. 371. Original union flatness
    of the combination is supplied by 4.1.12, p. 368. *)
Theorem current_flat_lipschitz_pushforward_linear c (T S:C)
    (hT:Flat T) (hS:Flat S):
  Push (c*:T+S) (@flat_current_linear_combination R h2 n m U hU c T S hT hS)=
    c*:Push T hT+Push S hS.
Proof.
have[K hKT]:=hT;have[L hLS]:=hS.
pose J:=smooth_compact_union K L.
have hKJ:smooth_compact_carrier K `<=` smooth_compact_carrier J by move=>x hx;left.
have hLJ:smooth_compact_carrier L `<=` smooth_compact_carrier J by move=>x hx;right.
have hTJ:=@flat_current_compact_monotone R h2 n m U hU K J hKJ T hKT.
have hSJ:=@flat_current_compact_monotone R h2 n m U hU L J hLJ S hLS.
have hCombination:(@flat_current_subspace R h2 n m U hU J) (c*:T+S).
  exact:(@subspace_add R C (@flat_current_subspace R h2 n m U hU J)
    (c*:T) S (@subspace_scale R C (@flat_current_subspace R h2 n m U hU J) c T hTJ) hSJ).
pose hGlobal:=@flat_current_linear_combination R h2 n m U hU c T S hT hS.
exact:(@current_compact_lipschitz_image_linear R h2 n nu m U V hU hV
  f hImage hLocal J c T S (Push T hT) (Push S hS) (Push (c*:T+S) hGlobal)
  hTJ hSJ ((Laws T hT).2 J hTJ) ((Laws S hS).2 J hSJ)
  ((Laws (c*:T+S) hGlobal).2 J hCombination)).
Qed.

(** Source for [current_flat_lipschitz_pushforward_congruence]:
    equal original flat currents have equal images, supporting
    the local cutoff definition in Federer 4.1.14, p. 371. *)
Lemma current_flat_lipschitz_pushforward_congruence
    (T S:C) (hT:Flat T) (hS:Flat S):T=S->Push T hT=Push S hS.
Proof.
move=>hEquality;subst S.
exact:current_flat_lipschitz_pushforward_proof_independent.
Qed.

(** Source for [current_flat_lipschitz_pushforward_subtract]:
    the original union image preserves differences, supporting
    cutoff independence in Federer 4.1.14, p. 371. *)
Lemma current_flat_lipschitz_pushforward_subtract
    (T S:C) (hT:Flat T) (hS:Flat S) (hDifference:Flat (T-S)):
  Push (T-S) hDifference=Push T hT-Push S hS.
Proof.
pose hCombination:=@flat_current_linear_combination R h2 n m U hU (-1) S T hS hT.
have hEquality:(-1:R)*:S+T=T-S by rewrite scaleN1r addrC.
have hCurrent:=@current_flat_lipschitz_pushforward_congruence
  ((-1:R)*:S+T) (T-S) hCombination hDifference hEquality.
have hLinear:=@current_flat_lipschitz_pushforward_linear (-1) S T hS hT.
apply:(eq_trans (esym hCurrent)).
apply:(eq_trans hLinear).
by rewrite scaleN1r addrC.
Qed.

(** Source for [current_flat_lipschitz_pushforward_support]:
    literal spt(f#T) is contained in f(spt T),
    Federer 4.1.14, p. 371. No flat membership
    with index spt T is assumed or inferred. *)
Theorem current_flat_lipschitz_pushforward_support (T:C) (hT:Flat T):
  @current_support R h2 nu V hV m (Push T hT) `<=`
    f @` @current_support R h2 n U hU m T.
Proof.
have[K hKT]:=hT.
exact:(@current_compact_lipschitz_image_support R h2 n nu m U V hU hV
  f hImage hLocal K T hKT _ ((Laws T hT).2 K hKT)).
Qed.

(** Source for [current_flat_lipschitz_pushforward_normal]:
    an original normal input has normal image,
    Federer 4.1.14, pp. 370–371. This follows
    from uniqueness of the normal construction. *)
Theorem current_flat_lipschitz_pushforward_normal (T:C) (hT:Flat T):
  @is_normal_current R h2 n U hU m T ->
  @is_normal_current R h2 nu V hV m (Push T hT).
Proof.
move=>hNormal;have[K hKT]:=hT.
have[Q [hNQ hQ]]:=@current_normal_lipschitz_image_exists R h2 n nu m U V hU hV
  f hImage hLocal K T hNormal (@flat_current_supported_support R h2 n m U hU K T hKT).
have hEquality:=@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV
  f hImage hLocal K T hKT (Push T hT) Q ((Laws T hT).2 K hKT) hQ.
by rewrite hEquality.
Qed.
End CurrentFlatLipschitzPushforwardBasic.
