(** Federer (1969), 4.1.14, p. 371: combine the
    compact-index maps on the original union F_m(U).
    The independent actual-current specification keeps
    every original compact index and its approximation
    law; no chosen index is part of the definition. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentCompactLipschitzPushforwardUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_flat_lipschitz_image]: the
    original f#T is flat and agrees with every
    compact-index definition, Federer 4.1.14, p. 371.
    Existence and uniqueness are proved separately. *)
Definition is_current_flat_lipschitz_image
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m) (Q:@current_space R h2 nu V hV m):Prop:=
  @is_flat_current R h2 nu m V hV Q /\
  forall (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U),
    @is_flat_current_supported_in R h2 n m U hU K T ->
    @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
      f hImage hLocal K T Q.
