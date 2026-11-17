(** Federer (1969), 3.4.12, p. 339: the original complex
    block inclusions are isometries. Connect the finite block identities
    to the standard Hermitian product, then apply the existing real
    triangle estimate for the product neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  FiniteCoordinates StandardHermitian HermitianRealImaginary HolomorphicCoordinateNorm
  InnerProductUP InnerNorm InnerNormInequalities HilbertFormCompactness
  FieldBlockCoordinates FieldBlockLinear FieldBlockLinearMaps Bilinear NormDifferentialUP RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section Norms.
Variable R:realType.
Variables v l:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space C (v+l)).
Local Notation V:=(coordinate_space C v).
Local Notation W:=(coordinate_space C l).
Local Notation NX:=(@holomorphic_coordinate_norm R (v+l)).
Local Notation NV:=(@holomorphic_coordinate_norm R v).
Local Notation NW:=(@holomorphic_coordinate_norm R l).

(** Source for [complex_block_join_inner]: the original Hermitian
    product splits over the complex coordinate blocks, supporting
    3.4.12, p. 339. Apply finite sum splitting and the checked
    original block coordinate evaluations. *)
Lemma complex_block_join_inner (u w:V*W):
  @standard_hermitian_product R (v+l) (field_block_join u) (field_block_join w)=
  @standard_hermitian_product R v u.1 w.1+@standard_hermitian_product R l u.2 w.2.
Proof.
rewrite /standard_hermitian_product big_split_ord.
congr (_+_);apply:eq_bigr=>i _;by rewrite ?field_block_join_left ?field_block_join_right.
Qed.
(** Source for [complex_block_join_real_inner]: the same block
    identity on the original underlying real space, used for
    its unchanged norm in 3.4.12, p. 339. *)
Lemma complex_block_join_real_inner (u w:V*W):
  hermitian_real_part (@standard_hermitian_product R (v+l)) (field_block_join u) (field_block_join w)=
  hermitian_real_part (@standard_hermitian_product R v) u.1 w.1+
  hermitian_real_part (@standard_hermitian_product R l) u.2 w.2.
Proof. by rewrite /hermitian_real_part complex_block_join_inner (complex_re_add (ComplexScalars.laws R)). Qed.

(** Source for [complex_first_injection_norm]: the first block is
    included isometrically, supporting the product neighbourhoods of
    Federer 3.1.18, p. 229. *)
Lemma complex_first_injection_norm (u:V) : NX (@field_first_injection C v l u)=NV u.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite inner_norm_sqr /field_first_injection complex_block_join_real_inner /=.
by rewrite (bil0l (inner_bilinear (hermitian_real_inner_product (@standard_hermitian_productP R l)))) addr0.
Qed.

(** Source for [complex_last_injection_norm]: the complementary block
    is included isometrically, supporting the product neighbourhoods of
    Federer 3.1.18, p. 229. *)
Lemma complex_last_injection_norm (w:W) : NX (@field_last_injection C v l w)=NW w.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite inner_norm_sqr /field_last_injection complex_block_join_real_inner /=.
by rewrite (bil0l (inner_bilinear (hermitian_real_inner_product (@standard_hermitian_productP R v)))) add0r.
Qed.

(** Source for [complex_product_box_in_ball]: a sufficiently small
    product of block balls lies in any ambient ball, supplying the
    convex neighbourhoods V,W in Federer 3.1.18, p. 229. *)
Lemma complex_product_box_in_ball (c x:X) r : 0<r ->
  NV (field_first_block x-field_first_block c)<r/3 ->
  NW (field_last_block x-field_last_block c)<r/3 -> NX (x-c)<r.
Proof.
move=>hr hv hw.
pose p:=@field_first_block_map C v l.
pose q:=@field_last_block_map C v l.
pose i:=@field_first_injection_map C v l.
pose j:=@field_last_injection_map C v l.
have he : x-c = i (p x-p c)+j (q x-q c).
  have h:=@field_block_linear_decomposition C v l (x-c).
  change (x-c = i (p (x-c))+j (q (x-c))) in h.
  rewrite (linB (hom_linear p) x c) (linB (hom_linear q) x c) in h.
  exact h.
rewrite he.
apply: le_lt_trans (inner_norm_triangle (hermitian_real_inner_product (@standard_hermitian_productP R (v+l))) _ _) _.
change (NX (@field_first_injection C v l (p x-p c))+
  NX (@field_last_injection C v l (q x-q c))<r).
rewrite complex_first_injection_norm complex_last_injection_norm.
by nra.
Qed.
End Norms.
