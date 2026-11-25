(** Federer (1969), 4.1.14, pp. 370–371: the
    original compact Lipschitz image first gives a linear
    map on the actual normal-current domain, with values
    in the exact flat space indexed by f(K). Its
    specification is independent of any chosen limits. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces NormalCurrentsUP NormalCurrentSpaces
  FlatCurrentSpaces CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_normal_lipschitz_pushforward]: the
    linear normal-current image with the full original
    approximation law, Federer 4.1.14, pp. 370–371.
    Neither a selected family nor the later bounded
    extension is part of this independent specification. *)
Definition is_current_normal_lipschitz_pushforward
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
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (P:Hom (@supported_normal_current_space R h2 n U hU m K)
      (@flat_current_space R h2 nu m V hV
        (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K))):Prop:=
  forall a,
    @is_normal_current R h2 nu V hV m
      (@flat_current_inclusion R h2 nu m V hV
        (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K) (P a)) /\
    @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
      f hImage hLocal K (@supported_normal_current_inclusion R h2 n U hU m K a)
      (@flat_current_inclusion R h2 nu m V hV
        (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K) (P a)).
