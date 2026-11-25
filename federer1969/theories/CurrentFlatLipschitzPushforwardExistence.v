(** Federer (1969), 4.1.14, p. 371: the
    original compatible compact-index maps define one
    flat-current image on their union. Any index
    is chosen only inside this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactLipschitzImageUniqueness CurrentCompactLipschitzImageCompatibility
  CurrentCompactLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFlatLipschitzPushforwardExistence.
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
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Local Notation Spec:=(@is_current_flat_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal T).

(** Source for [current_flat_lipschitz_pushforward_exists]:
    the original flat-current image exists on all
    F_m(U), Federer 4.1.14, p. 371, and retains
    every compact-index original approximation law. *)
Theorem current_flat_lipschitz_pushforward_exists:
  exists Q:@current_space R h2 nu V hV m,Spec Q.
Proof.
have[K hK]:=hFlat.
pose Q:=@CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal K T hK.
have hQ:=@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hImage hLocal K T hK.
exists Q;split.
- exists(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
  exact:hQ.1.
- move=>L hL.
  have hEquality:=@current_compact_lipschitz_pushforward_compatible R h2 n nu m U V hU hV
    f hImage hLocal K L T hK hL.
  rewrite /Q hEquality.
  exact:(@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hImage hLocal L T hL).
Qed.

(** Source for [current_flat_lipschitz_pushforward_unique]:
    the union map has one original actual value,
    Federer 4.1.14, p. 371. One existing compact
    index suffices to compare two candidates. *)
Theorem current_flat_lipschitz_pushforward_unique
    (Q P:@current_space R h2 nu V hV m):Spec Q->Spec P->Q = P.
Proof.
move=>hQ hP;have[K hK]:=hFlat.
exact:(@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV
  f hImage hLocal K T hK Q P (hQ.2 K hK) (hP.2 K hK)).
Qed.
End CurrentFlatLipschitzPushforwardExistence.
