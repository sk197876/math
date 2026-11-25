(** Federer (1969), 3.4.2(8), p. 316: changing one
    coordinate block preserves its original Euclidean distance. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  Bilinear InnerProductUP InnerNorm InnerMetric EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockLinearMaps EuclideanMetricProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_first_block_distance]: |(u,w)-(v,w)|
    equals |u-v|, supporting the flat increment in 3.4.2(8),
    p. 316. Both coordinate blocks may be empty. *)
Lemma critical_first_block_distance (R:realType) a b
    (u v:R_n R a) (w:R_n R b):
  inner_norm (@euclidean_inner_productP R (a+b))
    (euclidean_block_join (u,w)-euclidean_block_join (v,w))=
  inner_norm (@euclidean_inner_productP R a) (u-v).
Proof.
have hEq:euclidean_block_join (u,w)-euclidean_block_join (v,w)=
    euclidean_block_join (u-v,(0:R_n R b)).
  rewrite -euclidean_block_join_difference.
  congr euclidean_block_join;change ((u-v,w-w)=(u-v,0));by rewrite subrr.
rewrite hEq;apply:inner_norm_value;first exact:inner_norm_nonnegative.
by rewrite inner_norm_sqr euclidean_block_join_inner /=
  (bil0l (inner_bilinear (@euclidean_inner_productP R b))) addr0.
Qed.

(** Source for [critical_last_block_distance]: |(u,v)-(u,w)|
    equals |v-w|, supporting the transverse Lipschitz increment
    in 3.4.2(8), p. 316, including an empty transverse block. *)
Lemma critical_last_block_distance (R:realType) a b
    (u:R_n R a) (v w:R_n R b):
  inner_norm (@euclidean_inner_productP R (a+b))
    (euclidean_block_join (u,v)-euclidean_block_join (u,w))=
  inner_norm (@euclidean_inner_productP R b) (v-w).
Proof.
have hEq:euclidean_block_join (u,v)-euclidean_block_join (u,w)=
    euclidean_block_join ((0:R_n R a),v-w).
  rewrite -euclidean_block_join_difference.
  congr euclidean_block_join;change ((u-u,v-w)=(0,v-w));by rewrite subrr.
rewrite hEq;apply:inner_norm_value;first exact:inner_norm_nonnegative.
by rewrite inner_norm_sqr euclidean_block_join_inner /=
  (bil0l (inner_bilinear (@euclidean_inner_productP R a))) add0r.
Qed.
