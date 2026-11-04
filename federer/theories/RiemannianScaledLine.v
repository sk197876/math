(** Federer (1969), 3.2.46, pp. 281–282: a concrete constant
    tensor with length scale two, rather than the ordinary metric.
    Its intrinsic discriminant is computed through 1.7.10, p. 35. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates TensorUP Bilinear
  EuclideanInnerProduct RiemannianMetricCarrier InnerProductUP InnerProductPullback EuclideanLinearMaps
  BilinearRepresentativeUP BilinearInvariants PositiveNormFactorDiscriminant
  RiemannianTensorUP RiemannianConstantTensor RiemannianChartVolumeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_scaled_line_form]: a concrete g in
    Federer 3.2.46, p. 281, obtained by pulling the usual line
    inner product back along multiplication by two. *)
Definition riemannian_scaled_line_form (R:realType) (v w:R_n R 1):R:=
  @euclidean_inner_product R 1
    (euclidean_diagonal_map (fun _:'I_1=>(2:R)) v)
    (euclidean_diagonal_map (fun _:'I_1=>(2:R)) w).

(** Source for [riemannian_scaled_line_inner]: positivity of the
    concrete form used to test 3.2.46, p. 281. *)
Lemma riemannian_scaled_line_inner (R:realType):
  is_inner_product (@riemannian_scaled_line_form R).
Proof.
pose Q:=euclidean_diagonal_map (fun _:'I_1=>(2:R)).
have hQ:injective Q.
  apply/(euclidean_det_injective Q).
  by rewrite /Q euclidean_diagonal_det big_ord1 pnatr_eq0.
exact (@inner_product_linear_pullback R (R_n R 1) (R_n R 1)
  (@euclidean_inner_product R 1) (@euclidean_inner_productP R 1) Q hQ).
Qed.

(** Source for [riemannian_scaled_line_tensor]: a genuine
    continuous positive tensor on the whole line in
    3.2.46, p. 281, with non-Euclidean length scale. *)
Definition riemannian_scaled_line_tensor (R:realType):
  @is_continuous_riemannian_tensor R 1 setT
    (fun _=>@riemannian_scaled_line_form R):=
  riemannian_constant_tensor (riemannian_scaled_line_inner R).

(** Source for [riemannian_scaled_line_discriminant]: discr(g)= 4
    for this concrete tensor, calculated by the actual representative
    of 1.7.10, p. 35, as used in 3.2.46, p. 281. *)
Lemma riemannian_scaled_line_discriminant (R:realType)
    (hB:is_inner_product (@riemannian_scaled_line_form R)):
  euclidean_inner_form_discriminant hB= 4.
Proof.
pose F:=euclidean_diagonal_map (fun _:'I_1=>(4:R)).
have hRep:is_bilinear_representative (@euclidean_inner_product R 1)
    (@riemannian_scaled_line_form R) F.
  move=>v w; rewrite /F /riemannian_scaled_line_form /euclidean_inner_product !big_ord1.
  rewrite /euclidean_diagonal_map /euclidean_diagonal /= !ffunE.
  ring.
rewrite /euclidean_inner_form_discriminant
  (@bilinear_discriminant_characterisation R (euclidean_two_nonzero R) (R_n R 1)
    (@euclidean_inner_product R 1) (@riemannian_scaled_line_form R)
    (@euclidean_inner_productP R 1) (inner_bilinear hB) 1
    (@coordinate_basis R 1) (@coordinate_basisP R 1) F hRep).
change (euclidean_det F= 4).
by rewrite /F euclidean_diagonal_det big_ord1.
Qed.

(** Source for [riemannian_scaled_line_density]: the actual
    square-root discriminant equals two everywhere on this line,
    testing the volume and derivate formula in 3.2.46, pp. 281–282. *)
Lemma riemannian_scaled_line_density (R:realType)
    (x:riemannian_metric_space (riemannian_scaled_line_tensor R)):
  riemannian_chart_volume_density (riemannian_scaled_line_tensor R) x= 2.
Proof.
rewrite /riemannian_chart_volume_density riemannian_scaled_line_discriminant.
have hFour:(4:R)=(2:R)^+2 by ring.
by rewrite hFour sqrtr_sqr ger0_norm // ler0n.
Qed.
