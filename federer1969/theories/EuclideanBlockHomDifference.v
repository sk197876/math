(** Federer (1969), 3.2.47, pp. 282–283: supporting
    Frobenius isometry for the actual isotropy group. The difference
    of two extensions fixing the first block is zero there and is
    the original difference on the transverse block. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HomInner HomInnerCoordinates
  EuclideanHomInnerCharts EuclideanStiefelInnerSplitting
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  EuclideanBlockExtensionUP EuclideanBlockExtension ConcatenatedFamilies Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_block_basis_left]: supporting coordinate
    basis identity for the isotropy identification I with O(n-1)
    in 3.2.47, p. 282. It includes empty transverse blocks. *)
Lemma euclidean_block_basis_left (R:realType) a b (i:'I_a):
  @coordinate_basis R (a+b) (lshift b i)=
    euclidean_block_join (@coordinate_basis R a i,(0:R_n R b)).
Proof.
apply:euclidean_block_vectors_ext.
- move=>j; by rewrite euclidean_block_join_left /coordinate_basis !ffunE eq_lshift.
- move=>j; by rewrite euclidean_block_join_right /coordinate_basis !ffunE eq_rlshift.
Qed.

(** Source for [euclidean_block_basis_right]: supporting complementary
    coordinate identity for I isometric with O(n-1), 3.2.47,
    p. 282, including an empty first block. *)
Lemma euclidean_block_basis_right (R:realType) a b (i:'I_b):
  @coordinate_basis R (a+b) (rshift a i)=
    euclidean_block_join ((0:R_n R a),@coordinate_basis R b i).
Proof.
apply:euclidean_block_vectors_ext.
- move=>j; by rewrite euclidean_block_join_left /coordinate_basis !ffunE eq_lrshift.
- move=>j; by rewrite euclidean_block_join_right /coordinate_basis !ffunE eq_rshift.
Qed.

(** Source for [euclidean_block_extension_difference_inner]: actual
    Hom inner-product preservation for differences of transverse
    extensions, supporting the isotropy isometry in 3.2.47,
    pp. 282–283. Only the public block laws are used. *)
Theorem euclidean_block_extension_difference_inner (R:realType) a b
    (h g:Hom (R_n R b) (R_n R b)):
  let H:=hom_of_linear (@euclidean_block_extension R a b (hom_as_linear h)) in
  let G:=hom_of_linear (@euclidean_block_extension R a b (hom_as_linear g)) in
  euclidean_hom_inner_product (H-G) (H-G)=
    euclidean_hom_inner_product (h-g) (h-g).
Proof.
move=>H G.
rewrite /euclidean_hom_inner_product
  (@hom_inner_orthonormal_sum R (R_n R (a+b)) (R_n R (a+b))
    (@euclidean_inner_product R (a+b)) (@euclidean_inner_product R (a+b))
    (@euclidean_inner_productP R (a+b)) (@euclidean_inner_productP R (a+b))
    (a+b) (@coordinate_basis R (a+b)) (@coordinate_basisP R (a+b))
    (a+b) (@coordinate_basis R (a+b)) (@coordinate_basisP R (a+b))
    (@euclidean_coordinate_orthonormal_family R (a+b)))
  (@hom_inner_orthonormal_sum R (R_n R b) (R_n R b)
    (@euclidean_inner_product R b) (@euclidean_inner_product R b)
    (@euclidean_inner_productP R b) (@euclidean_inner_productP R b)
    b (@coordinate_basis R b) (@coordinate_basisP R b)
    b (@coordinate_basis R b) (@coordinate_basisP R b)
    (@euclidean_coordinate_orthonormal_family R b)) big_split_ord.
have hLeft (i:'I_a): (H-G) (@coordinate_basis R (a+b) (lshift b i))=0.
  rewrite euclidean_block_basis_left.
  change (@euclidean_block_extension R a b (hom_as_linear h)
    (euclidean_block_join (@coordinate_basis R a i,0))-
    @euclidean_block_extension R a b (hom_as_linear g)
    (euclidean_block_join (@coordinate_basis R a i,0))=0).
  by rewrite !euclidean_block_extension_specification !linear0 subrr.
have hRight (i:'I_b): (H-G) (@coordinate_basis R (a+b) (rshift a i))=
    euclidean_block_join ((0:R_n R a),h (@coordinate_basis R b i)-g (@coordinate_basis R b i)).
  rewrite euclidean_block_basis_right.
  change (@euclidean_block_extension R a b (hom_as_linear h)
    (euclidean_block_join (0,@coordinate_basis R b i))-
    @euclidean_block_extension R a b (hom_as_linear g)
    (euclidean_block_join (0,@coordinate_basis R b i))=
    euclidean_block_join ((0:R_n R a),h (@coordinate_basis R b i)-g (@coordinate_basis R b i))).
  rewrite !euclidean_block_extension_specification.
  apply/ffunP=>j; rewrite /euclidean_block_join !ffunE /concatenate_family.
  case:(split j)=>k /=; by rewrite !ffunE ?subrr.
have hSumLeft:(\sum_(i:'I_a) euclidean_inner_product
    ((H-G) (@coordinate_basis R (a+b) (lshift b i)))
    ((H-G) (@coordinate_basis R (a+b) (lshift b i))))=0.
  apply:big1=>i _; rewrite hLeft.
  change (euclidean_inner_product (0:R_n R (a+b)) 0=0).
  exact (bil0l (inner_bilinear (@euclidean_inner_productP R (a+b))) 0).
rewrite hSumLeft; etransitivity; first exact:add0r.
apply:eq_bigr=>i _.
rewrite !hRight euclidean_block_join_inner /=.
rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R a))) add0r.
have hEval:(h-g) (@coordinate_basis R b i)=h (@coordinate_basis R b i)-g (@coordinate_basis R b i).
  exact (linB (@hom_eval_linear R (R_n R b) (R_n R b) (@coordinate_basis R b i)) h g).
exact (congr2 (@euclidean_inner_product R b) (esym hEval) (esym hEval)).
Qed.

(** Source for [euclidean_block_extension_difference_norm]: the actual
    Frobenius distance of two transverse block extensions equals
    their original Frobenius distance; supporting the isotropy
    isometry of 3.2.47, pp. 282–283. *)
Corollary euclidean_block_extension_difference_norm (R:realType) a b
    (h g:Hom (R_n R b) (R_n R b)):
  inner_norm (@euclidean_hom_inner_productP R (a+b) (a+b))
    (hom_of_linear (@euclidean_block_extension R a b (hom_as_linear h))-
     hom_of_linear (@euclidean_block_extension R a b (hom_as_linear g)))=
  inner_norm (@euclidean_hom_inner_productP R b b) (h-g).
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr; symmetry; exact:euclidean_block_extension_difference_inner.
Qed.
