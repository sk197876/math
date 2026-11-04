(** Public graph of sqrt(discr g) in Federer (1969), 3.2.46,
    pp. 281--282. Use independent laws only; no global frozen frame
    is selected and no Hausdorff-measure formula is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations RealMetricBackground
  PartialFunctionUP RiemannianTensorUP RiemannianVolumeDensityUP
  RiemannianVolumeDensitySealed PositiveSymmetricNormFactor
  PositiveNormFactorDiscriminant EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_density]: the actual original-
    domain function sqrt(discr(g)) in Federer 3.2.46, pp. 281--282. *)
Definition riemannian_volume_density (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :=
  @RiemannianVolumeDensity.value R n A g hg.

(** Source for [riemannian_volume_density_laws]: exact public
    graph laws for sqrt(discr g), Federer 3.2.46, pp. 281--282. *)
Lemma riemannian_volume_density_laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  is_riemannian_volume_density hg (riemannian_volume_density hg).
Proof. exact: RiemannianVolumeDensity.laws. Qed.

(** Source for [riemannian_volume_density_domain]: the original
    coordinate domain A is exactly the domain of the printed
    density function, Federer 3.2.46, pp. 281--282. *)
Lemma riemannian_volume_density_domain (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  partial_function_domain (riemannian_volume_density hg) = A.
Proof.
apply/seteqP; split=> x.
- move=> [z hz]; have [hx _] := (riemannian_volume_density_laws hg x z).1 hz.
  exact hx.
- move=> hx; exists (Num.sqrt (euclidean_inner_form_discriminant
    (riemannian_tensor_inner hg hx))).
  apply/(riemannian_volume_density_laws hg); by exists hx.
Qed.

(** Source for [riemannian_volume_density_factor_value]: the
    actual local det(L) gives exactly the density value in Federer
    3.2.46, p. 281, without selecting L at other points. *)
Lemma riemannian_volume_density_factor_value (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x)
    (L : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor (riemannian_tensor_inner hg hx) L ->
  partial_function_graph (riemannian_volume_density hg) x (euclidean_det L).
Proof.
move=> hL; apply/(riemannian_volume_density_laws hg); exists hx.
exact: positive_norm_factor_discriminant hL.
Qed.

(** Source for [riemannian_volume_density_positive]: the printed
    density is finite and strictly positive everywhere on A,
    supporting Federer 3.2.46, pp. 281--282. Empty domains and
    the positive degree-zero determinant are retained. *)
Lemma riemannian_volume_density_positive (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) :
  exists r : R, 0 < r /\
    partial_function_graph (riemannian_volume_density hg) x r.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists (riemannian_tensor_inner hg hx).
exists (euclidean_det L); split; first exact: positive_norm_factor_det_positive hL.
exact: riemannian_volume_density_factor_value hL.
Qed.
