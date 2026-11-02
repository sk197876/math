(** Federer (1969), 3.1.18, p. 229: choose a product of convex
    neighbourhoods inside the open image of the local inverse theorem.
    The block inclusions are isometries, including empty blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormInequalities HilbertFormCompactness
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  Bilinear NormDifferentialUP RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Norms.
Variable R:realType.
Variables v l:nat.
Local Notation X:=(R_n R (v+l)).
Local Notation V:=(R_n R v).
Local Notation W:=(R_n R l).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (v+l))).
Local Notation NV:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NW:=(inner_norm (@euclidean_inner_productP R l)).

(** Source for [euclidean_first_injection_norm]: the first block is
    included isometrically, supporting the product neighbourhoods of
    Federer 3.1.18, p. 229. *)
Lemma euclidean_first_injection_norm (u:V) : NX (@euclidean_first_injection R v l u)=NV u.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite inner_norm_sqr /euclidean_first_injection euclidean_block_join_inner /=.
by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R l))) addr0.
Qed.

(** Source for [euclidean_last_injection_norm]: the complementary block
    is included isometrically, supporting the product neighbourhoods of
    Federer 3.1.18, p. 229. *)
Lemma euclidean_last_injection_norm (w:W) : NX (@euclidean_last_injection R v l w)=NW w.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite inner_norm_sqr /euclidean_last_injection euclidean_block_join_inner /=.
by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R v))) add0r.
Qed.

(** Source for [euclidean_product_box_in_ball]: a sufficiently small
    product of block balls lies in any ambient ball, supplying the
    convex neighbourhoods V,W in Federer 3.1.18, p. 229. *)
Lemma euclidean_product_box_in_ball (c x:X) r : 0<r ->
  NV (euclidean_first_block x-euclidean_first_block c)<r/3 ->
  NW (euclidean_last_block x-euclidean_last_block c)<r/3 -> NX (x-c)<r.
Proof.
move=>hr hv hw.
pose p:=@euclidean_first_block_map R v l.
pose q:=@euclidean_last_block_map R v l.
pose i:=@euclidean_first_injection_map R v l.
pose j:=@euclidean_last_injection_map R v l.
have he : x-c = i (p x-p c)+j (q x-q c).
  have h:=@euclidean_block_linear_decomposition R v l (x-c).
  change (x-c = i (p (x-c))+j (q (x-c))) in h.
  rewrite (linB (hom_linear p) x c) (linB (hom_linear q) x c) in h.
  exact h.
rewrite he.
apply: le_lt_trans (inner_norm_triangle (@euclidean_inner_productP R (v+l)) _ _) _.
change (NX (@euclidean_first_injection R v l (p x-p c))+
  NX (@euclidean_last_injection R v l (q x-q c))<r).
rewrite euclidean_first_injection_norm euclidean_last_injection_norm.
by nra.
Qed.
End Norms.
