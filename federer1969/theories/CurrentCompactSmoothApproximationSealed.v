(** Federer (1969), 4.1.14, p. 370: the chosen source neighbourhood
    and smooth approximating sequence are opaque. Only their independent
    class, image, sharp bound and uniform convergence laws are public.
    Existence is proved before selecting this one pair of witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP SmoothCompactSet
  LipschitzUP CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type CurrentCompactSmoothApproximationSignature.
(** Source for [value]: one source neighbourhood and one sequence of
    approximants from Federer 4.1.14, p. 370. The sharp bound may be zero. *)
Parameter value:forall (R:realType) (n nu:nat)
  (U:set (R_n R n)) (V:set (R_n R nu))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
  (f:R_n R n->R_n R nu) (L:R)
  (hBoundK:@is_metric_lipschitz_bound R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
    (smooth_compact_carrier K) f L)
  (hImageK:forall x,smooth_compact_carrier K x->V (f x)),
  (set (R_n R n))*(nat->R_n R n->R_n R nu).
(** Source for [laws]: the complete independently specified approximating
    family from Federer 4.1.14, p. 370; its construction stays hidden. *)
Parameter laws:forall (R:realType) (n nu:nat)
  (U:set (R_n R n)) (V:set (R_n R nu))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
  (f:R_n R n->R_n R nu) (L:R)
  (hBoundK:@is_metric_lipschitz_bound R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
    (smooth_compact_carrier K) f L)
  (hImageK:forall x,smooth_compact_carrier K x->V (f x)),
  @is_current_compact_smooth_approximation R n nu U V K f L
    (@value R n nu U V hU hV K f L hBoundK hImageK).1
    (@value R n nu U V hU hV K f L hBoundK hImageK).2.
End CurrentCompactSmoothApproximationSignature.
Module CurrentCompactSmoothApproximation:CurrentCompactSmoothApproximationSignature.
(** Source for [value]: seal one proved approximating pair, supporting
    Federer 4.1.14, p. 370. No mathematical property is postulated. *)
Definition value (R:realType) (n nu:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu) (L:R)
    (hBoundK:@is_metric_lipschitz_bound R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      (smooth_compact_carrier K) f L)
    (hImageK:forall x,smooth_compact_carrier K x->V (f x)):
    (set (R_n R n))*(nat->R_n R n->R_n R nu):=
  projT1 (cid (@current_compact_smooth_approximation_data_exists R n nu
    U V hU hV K f L hBoundK hImageK)).
(** Source for [laws]: the sealed pair has the independent original
    approximation laws, supporting Federer 4.1.14, p. 370. *)
Lemma laws (R:realType) (n nu:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu) (L:R)
    (hBoundK:@is_metric_lipschitz_bound R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      (smooth_compact_carrier K) f L)
    (hImageK:forall x,smooth_compact_carrier K x->V (f x)):
  @is_current_compact_smooth_approximation R n nu U V K f L
    (@value R n nu U V hU hV K f L hBoundK hImageK).1
    (@value R n nu U V hU hV K f L hBoundK hImageK).2.
Proof.
exact:(projT2 (cid (@current_compact_smooth_approximation_data_exists R n nu
  U V hU hV K f L hBoundK hImageK))).
Qed.
End CurrentCompactSmoothApproximation.
