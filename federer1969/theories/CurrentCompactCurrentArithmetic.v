(** Federer (1969), 4.1.11, pp. 365–366: zero and scalar
    operations on the compact currents used in the signed join
    and simplex formulas. Reuse the preceding support and proper
    pushforward linearity laws; no current space is reconstructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentSupportGeometry SmoothCompactSet CurrentCompactSmoothAlgebra
  CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_compact_zero_support]: the zero
    current has compact empty support, supporting the scalar
    manipulations of Federer 4.1.11, pp. 365–366. This is the
    preceding support bound applied to the empty compact set. *)
Theorem current_compact_zero_support (R:realType) (h2:(1+1:R)!=0)
    n k (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U hU k (0:@current_space R h2 n U hU k)).
Proof.
pose K:=@smooth_compact_empty R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
exact:(@current_support_compact_bound R h2 n k U hU K 0
  (@current_support_zero_subset R h2 n k U hU K)).
Qed.

(** Source for [current_compact_scaled_support]: scaling an
    original compact current preserves compact support, supporting
    the signs in Federer 4.1.11, pp. 365–366. Reuse the preceding
    compact linear-combination law with the zero current. *)
Theorem current_compact_scaled_support (R:realType) (h2:(1+1:R)!=0)
    n k (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU k) c:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U hU k T)->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U hU k (c*:T)).
Proof.
move=>hT.
have h:=@current_compact_linear_support R h2 n k U hU c T 0 hT
  (@current_compact_zero_support R h2 n k U hU).
by rewrite addr0 in h.
Qed.

(** Source for [current_compact_map_scaled_image]: the
    original compact image satisfies f#(cT)=c f#T, supporting
    the signed join identities of Federer 4.1.11, p. 365. Every
    compactness witness is permitted; use the earlier linearity
    and zero-image theorems. *)
Theorem current_compact_map_scaled_image (R:realType) (h2:(1+1:R)!=0)
    m n (U:set (R_n R m)) (V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R m->R_n R n) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    k (T:@current_space R h2 m U hU k) c
    (hT:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k T))
    (hScaled:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k (c*:T))):
  @current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k (c*:T) hScaled=
    c*:@current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT.
Proof.
pose h0:=@current_compact_zero_support R h2 m k U hU.
have hSum:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@current_support R h2 m U hU k (c*:T+0)) by rewrite addr0.
have h:=@current_compact_map_pushforward_linear R h2 m n U V hU hV
  f hImage hf k c T 0 hT h0 hSum.
have hCompare:=@current_compact_map_pushforward_congruence R h2 m n U V hU hV
  f hImage hf k (c*:T+0) (c*:T) hSum hScaled (addr0 (c*:T)).
have hZero:=@current_compact_map_pushforward_zero R h2 m n U V hU hV
  f hImage hf k 0 h0 (erefl 0).
by rewrite hCompare hZero addr0 in h.
Qed.
