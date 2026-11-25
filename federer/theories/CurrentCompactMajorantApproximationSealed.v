(** Federer (1969), 4.1.14, pp. 371–372: opaque selection of
    the proved smooth family preserving the continuous actual
    almost-everywhere differential majorant. Its construction and
    all cutoff, directional and convolution witnesses remain hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  SmoothCompactSet LipschitzUP CurrentCompactMajorantApproximationUP
  CurrentCompactMajorantApproximationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type CurrentCompactMajorantApproximationSignature.
(** Source for [value]: one neighbourhood, smooth family and
    positive vanishing error sequence, Federer 4.1.14, pp. 371–372. *)
Parameter value:forall (R:realType) (n nu:nat)
  (U:set (R_n R n)) (V:set (R_n R nu))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
  (f:R_n R n->R_n R nu) (sigma:R_n R n->R^o)
  (hLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
  (hImage:forall x,U x->V (f x))
  (hSigma:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) U sigma)
  (hMajorant:@is_current_ae_differential_majorant R n nu U f sigma),
  (set (R_n R n))*((nat->R_n R n->R_n R nu)*(nat->R)).
(** Source for [laws]: the independently specified original smooth
    approximation and pointwise cap on K, Federer 4.1.14, pp. 371–372. *)
Parameter laws:forall (R:realType) (n nu:nat)
  (U:set (R_n R n)) (V:set (R_n R nu))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
  (f:R_n R n->R_n R nu) (sigma:R_n R n->R^o)
  (hLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
  (hImage:forall x,U x->V (f x))
  (hSigma:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) U sigma)
  (hMajorant:@is_current_ae_differential_majorant R n nu U f sigma),
  @is_current_compact_majorant_smooth_approximation R n nu U V K f sigma
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).1
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).2.1
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).2.2.
End CurrentCompactMajorantApproximationSignature.
Module CurrentCompactMajorantApproximation:CurrentCompactMajorantApproximationSignature.
(** Source for [value]: seal the independently proved approximating
    triple from Federer 4.1.14, pp. 371–372. *)
Definition value (R:realType) (n nu:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu) (sigma:R_n R n->R^o)
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hImage:forall x,U x->V (f x))
    (hSigma:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) U sigma)
    (hMajorant:@is_current_ae_differential_majorant R n nu U f sigma):
    (set (R_n R n))*((nat->R_n R n->R_n R nu)*(nat->R)):=
  projT1 (cid (@current_compact_majorant_approximation_data_exists R n nu
    U V hU hV K f sigma hLocal hImage hSigma hMajorant)).
(** Source for [laws]: the sealed triple has every independent
    original approximation law, Federer 4.1.14, pp. 371–372. *)
Lemma laws (R:realType) (n nu:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu) (sigma:R_n R n->R^o)
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hImage:forall x,U x->V (f x))
    (hSigma:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) U sigma)
    (hMajorant:@is_current_ae_differential_majorant R n nu U f sigma):
  @is_current_compact_majorant_smooth_approximation R n nu U V K f sigma
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).1
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).2.1
    (@value R n nu U V hU hV K f sigma hLocal hImage hSigma hMajorant).2.2.
Proof.
exact:(projT2 (cid (@current_compact_majorant_approximation_data_exists R n nu
  U V hU hV K f sigma hLocal hImage hSigma hMajorant))).
Qed.
End CurrentCompactMajorantApproximation.
