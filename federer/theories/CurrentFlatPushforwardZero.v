(** Federer (1969), 4.1.15, p. 373: the affine-plane
    support corollary uses the fact that the flat image
    of zero is zero. Derive it from the actual
    linearity of 4.1.14, p. 371; the original
    membership proof does not affect the image. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP FlatCurrentUnion
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_pushforward_zero]: f#0=0,
    by the formal properties of 4.1.14, p. 371,
    as used in the affine-subspace consequence of
    Federer 4.1.15, p. 373. Empty opens and
    arbitrary evidence of flat membership are retained. *)
Theorem current_flat_lipschitz_pushforward_zero (R:realType)
    (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hFlat:@is_flat_current R h2 n m U hU 0):
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal 0 hFlat=0.
Proof.
pose hCombination:=@flat_current_linear_combination R h2 n m U hU (-1) 0 0 hFlat hFlat.
have hSource:(-1:R)*:(0:@current_space R h2 n U hU m)+0=0.
  by rewrite scaleN1r oppr0 add0r.
have hValue:=@current_flat_lipschitz_pushforward_congruence R h2 n nu m
  U V hU hV f hImage hLocal ((-1:R)*:0+0) 0 hCombination hFlat hSource.
have hLinear:=@current_flat_lipschitz_pushforward_linear R h2 n nu m
  U V hU hV f hImage hLocal (-1) 0 0 hFlat hFlat.
apply:(eq_trans (esym hValue)).
apply:(eq_trans hLinear).
by rewrite scaleN1r addNr.
Qed.

Arguments current_flat_lipschitz_pushforward_zero : clear implicits.
