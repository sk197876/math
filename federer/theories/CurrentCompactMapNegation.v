(** Federer (1969), 4.1.11, p. 366: affine
    transport preserves the negative simplex. This is
    the preceding proper-pushforward linearity, retaining
    every compactness witness and original open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactPushforwardAlgebra CurrentCompactCurrentArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_compact_map_negative_image]: the
    original f#(-T)=-f#T on compact currents, supporting
    the simplex orientation transfer in Federer 4.1.11,
    p. 366. No representation hypothesis is added. *)
Theorem current_compact_map_negative_image (R:realType) (h2:(1+1:R)!=0) m n
    (U:set (R_n R m)) (V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R m->R_n R n) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    k (T:@current_space R h2 m U hU k)
    (hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k T))
    (hNegative:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k (-T))):
  @current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k (-T) hNegative=
    -@current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT.
Proof.
pose hScaled:=@current_compact_scaled_support R h2 m k U hU T (-1:R) hT.
have hScale:=@current_compact_map_scaled_image R h2 m n U V hU hV f hImage hf k T (-1:R) hT hScaled.
have hInput:=@current_compact_map_pushforward_congruence R h2 m n U V hU hV f hImage hf
  k ((-1:R)*:T) (-T) hScaled hNegative (scaleN1r T).
by rewrite hInput scaleN1r in hScale.
Qed.
