(** Federer (1969), 4.1.14, pp. 371–372: seal the
    original affine chain h#([0,1] times T) when only
    the segments over sptT have to lie in V.
    The original independent neighbourhood law is public;
    the witness and all neighbourhood choices are hidden.
    Constructions serve solely to prove existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentLipschitzAffineChainUP
  CurrentLipschitzAffineChainExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentLipschitzAffineChainSignature.
(** Source for [value]: the original affine chain as
    an actual current, Federer 4.1.14, p. 372,
    with the segment-image condition only on sptT. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
      V ((1-t)*:f x+t*:g x)),
  @current_space R h2 nu V hV (1+m)%N.
(** Source for [laws]: every allowed original source
    neighbourhood computes the same affine chain, supporting
    Federer 4.1.14, pp. 371–372. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
      V ((1-t)*:f x+t*:g x)),
  @is_current_lipschitz_affine_chain R h2 n nu m U V hU hV f g
    hFLocal hGLocal T (@value R h2 n nu m U V hU hV f g hFLocal hGLocal T hFlat hBand).
End CurrentLipschitzAffineChainSignature.

Module CurrentLipschitzAffineChain:CurrentLipschitzAffineChainSignature.
(** Source for [value]: hide the independently proved
    witness of Federer 4.1.14, p. 372. No
    chosen approximation or neighbourhood is exposed. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
      V ((1-t)*:f x+t*:g x)):
  @current_space R h2 nu V hV (1+m)%N:=
  projT1 (cid (@current_lipschitz_affine_chain_exists R h2 n nu m U V hU hV f g hFLocal hGLocal T hFlat hBand)).
(** Source for [laws]: the opaque chain satisfies
    its independent original neighbourhood law, supporting
    Federer 4.1.14, pp. 371–372. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
      V ((1-t)*:f x+t*:g x)):
  @is_current_lipschitz_affine_chain R h2 n nu m U V hU hV f g
    hFLocal hGLocal T (@value R h2 n nu m U V hU hV f g hFLocal hGLocal T hFlat hBand).
Proof.
exact:(projT2 (cid (@current_lipschitz_affine_chain_exists R h2 n nu m U V hU hV f g hFLocal hGLocal T hFlat hBand))).
Qed.
End CurrentLipschitzAffineChain.

Arguments CurrentLipschitzAffineChain.value : clear implicits.
Arguments CurrentLipschitzAffineChain.laws : clear implicits.
