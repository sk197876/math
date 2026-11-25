(** The original block coordinates of the anisotropic
    maps in Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  Bilinear InnerProductUP InnerProductLaws EuclideanLinearMaps EuclideanBlockCoordinates EuclideanBlockLinear ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_prefix_stretch_block]: supporting
    exact coordinate action in Federer 3.2.45,
    pp. 279–280. The existing diagonal map sends
    the original pair (x,y) to (h*x,y).
    Every real h and either empty block remain. *)
Lemma euclidean_prefix_stretch_block (R : realType) m n (h : R)
    (x : R_n R m) (y : R_n R n) :
  @euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then h else 1)
    (@euclidean_block_join R m n (x,y))= @euclidean_block_join R m n (h*:x,y).
Proof.
apply: euclidean_block_vectors_ext.
- move=> i; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE ?euclidean_block_join_left ?concatenate_family_l.
  have hIndex : (lshift n i<m)%N := ltn_ord i.
  by rewrite hIndex ffunE.
- move=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE ?euclidean_block_join_right ?concatenate_family_r.
  have hIndex : (rshift m j<m)%N=false.
    change ((m+j<m)%N=false); by rewrite ltnNge leq_addr.
  by rewrite hIndex mul1r.
Qed.

(** Source for [euclidean_block_zero_first_norm]: supporting
    norm of the original vertical increments in Federer
    3.2.45, p. 279. The existing block inner
    product is the sum of the two component products;
    its zero first component leaves exactly the original
    second norm, including dimension zero. *)
Lemma euclidean_block_zero_first_norm (R : realType) m n (y : R_n R n) :
  inner_norm (@euclidean_inner_productP R (m+n)) (@euclidean_block_join R m n (0,y))=
    inner_norm (@euclidean_inner_productP R n) y.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite euclidean_block_join_inner (bil0l (inner_bilinear (@euclidean_inner_productP R m))) add0r inner_norm_sqr.
Qed.

(** Source for [euclidean_block_right_norm_bound]: supporting
    original vertical foot bound in Federer 3.2.45,
    p. 279. The existing orthogonal block inner
    product and nonnegative first squared norm prove
    that the second norm is at most the whole
    norm. Thin or zero-dimensional blocks need no
    additional condition. *)
Lemma euclidean_block_right_norm_bound (R : realType) m n
    (x : R_n R m) (y : R_n R n) :
  inner_norm (@euclidean_inner_productP R n) y<=
    inner_norm (@euclidean_inner_productP R (m+n)) (@euclidean_block_join R m n (x,y)).
Proof.
rewrite -(ler_sqr (inner_norm_nonnegative (@euclidean_inner_productP R n) y)
  (inner_norm_nonnegative (@euclidean_inner_productP R (m+n)) _)).
rewrite !inner_norm_sqr euclidean_block_join_inner.
change (is_true (euclidean_inner_product y y<=euclidean_inner_product x x+euclidean_inner_product y y)).
rewrite lerDr; exact: (inner_nonnegative (@euclidean_inner_productP R m) x).
Qed.

(** Source for [euclidean_block_vertical_increment]: supporting
    original section-tube identity in Federer 3.2.45,
    p. 279. Adding an original zero-first-block
    increment preserves the first coordinate. This
    is the existing block linearity law at scalar
    one, with no selected coordinate chart. *)
Lemma euclidean_block_vertical_increment (R : realType) m n
    (x : R_n R m) (y z : R_n R n) :
  @euclidean_block_join R m n (x,y)+@euclidean_block_join R m n (0,z)=
    @euclidean_block_join R m n (x,y+z).
Proof.
have h := @euclidean_block_join_linear R m n 1 (x,y) (0,z).
rewrite !scale1r in h.
change (@euclidean_block_join R m n (x+0,y+z)=
  @euclidean_block_join R m n (x,y)+@euclidean_block_join R m n (0,z)) in h.
by rewrite addr0 in h.
Qed.
