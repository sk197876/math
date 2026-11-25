(** Federer (1969), 4.1.14, pp. 370–371: the exact compact
    index f(K) and unchanged compact source indices on smaller
    open neighbourhoods. These are the existing compact-index
    operations, without enlarging the original sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  NormClassOneUP LipschitzUP OpenLocalLipschitzCompact
  SmoothCompactSet SmoothCompactImage CurrentSpaces CurrentSupportGeometry
  FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_index_in_open]: the same original
    compact K in the open source neighbourhood Z, Federer
    4.1.14, p. 370. Only its containment evidence changes. *)
Definition current_compact_index_in_open (R:realType) n
    (U Z:set (R_n R n))
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKZ:smooth_compact_carrier K `<=` Z):
    smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) Z:=
  @Build_smooth_compact_set R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) Z
    (smooth_compact_carrier K) hKZ (smooth_compact_is_compact K).

(** Source for [current_compact_index_in_open_carrier]: replacing
    U by Z keeps exactly K, Federer 4.1.14, p. 370. *)
Lemma current_compact_index_in_open_carrier (R:realType) n
    (U Z:set (R_n R n))
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKZ:smooth_compact_carrier K `<=` Z):
  smooth_compact_carrier (@current_compact_index_in_open R n U Z K hKZ)=
    smooth_compact_carrier K.
Proof. by []. Qed.

(** Source for [current_lipschitz_compact_image]: precisely f(K)
    in the original target V, Federer 4.1.14, pp. 370–371.
    Continuity is derived from the original local Lipschitz
    hypothesis; neither a global bound nor convexity is required. *)
Definition current_lipschitz_compact_image (R:realType) n nu
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
    smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) V:=
  @smooth_compact_image R (R_n R n) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) U V f hImage
    (@norm_open_local_lipschitz_class_zero R (R_n R n) (R_n R nu)
      (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R nu))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f hU hLocal) K.

(** Source for [current_lipschitz_compact_image_carrier]: the target
    compact index is the exact original f(K), Federer 4.1.14,
    p. 370. No compact neighbourhood replaces its carrier. *)
Lemma current_lipschitz_compact_image_carrier (R:realType) n nu
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  smooth_compact_carrier
    (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)=
    f @` smooth_compact_carrier K.
Proof. by []. Qed.

(** Source for [flat_supported_current_compact]: every original
    member of F_(m,K)(U) has compact support, by 4.1.12,
    p. 368; supporting the smooth images in the defining
    convergence condition of 4.1.14, p. 370. *)
Theorem flat_supported_current_compact (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m):
  @is_flat_current_supported_in R h2 n m U hU K T->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U hU m T).
Proof.
move=>hT;apply:(@current_support_compact_bound R h2 n m U hU K T).
exact:(@flat_current_supported_support R h2 n m U hU K T hT).
Qed.
