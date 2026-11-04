(** Federer (1969), 3.2.46, p. 281: the determinant of the local
    positive symmetric map is the square root of the discriminant.
    All numbers use the existing intrinsic determinant and bilinear
    representative of 1.7.10; no matrix determinant is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import TensorUP Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm
  PrincipalAxesUP SymmetricEndomorphisms EuclideanLinearMaps ExteriorDeterminant
  BilinearRepresentativeUP BilinearInvariants BasisEigenvalueDeterminant
  PositiveSymmetricNormFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_inner_form_discriminant]: discr(g(a)) in
    Federer 3.2.46, p. 281, using the abstract definition of 1.7.10,
    p. 35, relative to the ordinary Euclidean inner product. *)
Definition euclidean_inner_form_discriminant (R : realType) n
    (B : R_n R n -> R_n R n -> R) (hB : is_inner_product B) :=
  @bilinear_discriminant R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) B (@euclidean_inner_productP R n)
    (inner_bilinear hB) n (@coordinate_basis R n) (@coordinate_basisP R n).

(** Source for [positive_norm_factor_pair]: the local L transports
    the whole frozen inner product, supporting Federer 3.2.46, p. 281.
    Its norm law and real polarization prove the pair identity. *)
Lemma positive_norm_factor_pair (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L -> forall u v,
    @euclidean_inner_product R n (L u) (L v) = B u v.
Proof.
move=> hL u v.
have hU := congr1 (fun r : R => r^+2) (positive_norm_factor_norm hL u).
have hV := congr1 (fun r : R => r^+2) (positive_norm_factor_norm hL v).
have hSum := congr1 (fun r : R => r^+2) (positive_norm_factor_norm hL (u+v)).
rewrite !inner_norm_sqr in hU hV hSum.
rewrite linearD (inner_sum_square (@euclidean_inner_productP R n))
  (inner_sum_square hB) in hSum.
nra.
Qed.

(** Source for [positive_norm_factor_det_positive]: det(L)>0,
    supporting Federer 3.2.46, p. 281. The actual axes retained
    by the local factor give positive eigenvalues, including the
    empty-product determinant one in dimension zero. *)
Lemma positive_norm_factor_det_positive (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L -> 0 < euclidean_det L.
Proof.
move=> hL; have [e [he [hON hAxes]]] := positive_norm_factor_axes hL.
rewrite /euclidean_det (det_basis_independent (euclidean_two_nonzero R)
  (@coordinate_basisP R n) he).
exact: (@positive_basis_eigenvalue_determinant R (euclidean_two_nonzero R)
  (R_n R n) n e he L (fun i => inner_norm hB (e i))
  (fun i => (hAxes i).1) (fun i => (hAxes i).2)).
Qed.

(** Source for [positive_norm_factor_discriminant]: the printed
    det(L)=sqrt(discr(g(a))) in Federer 3.2.46, p. 281. Symmetry
    and the pair law show that L composed with L is the actual
    bilinear representative; multiplicativity gives the square. *)
Theorem positive_norm_factor_discriminant (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L ->
  euclidean_det L = Num.sqrt (euclidean_inner_form_discriminant hB).
Proof.
move=> hL.
have hRep : is_bilinear_representative (@euclidean_inner_product R n) B
    (linear_comp L L).
  move=> u v; change (@euclidean_inner_product R n (L (L u)) v = B u v).
  rewrite (positive_norm_factor_symmetric hL).
  exact: (@positive_norm_factor_pair R n B hB L hL u v).
have hSquare : euclidean_inner_form_discriminant hB = (euclidean_det L)^+2.
  rewrite /euclidean_inner_form_discriminant
    (@bilinear_discriminant_characterisation R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) B (@euclidean_inner_productP R n)
      (inner_bilinear hB) n (@coordinate_basis R n) (@coordinate_basisP R n)
      (linear_comp L L) hRep).
  rewrite det_comp /euclidean_det expr2; by [].
rewrite hSquare sqrtr_sqr ger0_norm; first by [].
exact: ltW (positive_norm_factor_det_positive hL).
Qed.
