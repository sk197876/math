(** Federer (1969), 3.2.46, p. 282: the
    source volume density cancels the source-inner-product
    normalization in the actual area Jacobian. This is an
    exact linear algebra identity, including singular maps
    and the zero-dimensional empty product. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerProductUP
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant OrthogonalMaps
  FiniteInnerChartUP FiniteInnerExteriorJacobianChart EuclideanLinearJacobian
  TopMiddleJacobianComposition ExteriorDeterminant RiemannianLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_jacobian_target_coordinates]:
    an actual target isometry M computes the same Jacobian
    as M composed F, with ordinary Euclidean source metric,
    supporting the area/coarea extension in 3.2.46, p. 282.
    No inverse target map or global frame field is needed. *)
Lemma riemannian_jacobian_target_coordinates (R : realType) m n C
    (hC : @is_inner_product R (R_n R n) C)
    (M : {linear R_n R n -> R_n R n}) k
    (F : Hom (R_n R m) (R_n R n)) :
  is_positive_symmetric_norm_factor hC M ->
  riemannian_linear_jacobian (@euclidean_inner_productP R m) hC k F =
    euclidean_linear_jacobian k (hom_comp (hom_of_linear M) F).
Proof.
move=> hM.
pose idM := hom_of_linear (linear_id (R_n R m)).
have hChart : is_finite_inner_chart (@euclidean_inner_product R m) idM idM.
  constructor; by move=> x.
have hIsometry : is_orthogonal_map C (@euclidean_inner_product R n) M.
  exact: positive_norm_factor_pair hM.
have h := @finite_inner_chart_exterior_jacobian R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) C (@euclidean_inner_productP R m) hC m n
  idM idM (hom_of_linear M) F k
  (riemannian_linear_jacobian (@euclidean_inner_productP R m) hC k F)
  hChart hIsometry (riemannian_linear_jacobian_laws (@euclidean_inner_productP R m) hC k F).
have hMap : hom_comp (hom_of_linear M) (hom_comp F idM)=hom_comp (hom_of_linear M) F.
  apply: hom_ext=> x; by [].
by rewrite hMap in h; exact: esym h.
Qed.

(** Source for [riemannian_area_jacobian_volume_factor]:
    J_{B,C}^m(F) sqrt(discr B) = J_{Euclidean,C}^m(F),
    the source normalization cancellation used in 3.2.46,
    p. 282. Every rank and natural dimension is retained. *)
Theorem riemannian_area_jacobian_volume_factor (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C)
    (F : Hom (R_n R m) (R_n R n)) :
  riemannian_linear_jacobian hB hC m F * Num.sqrt (euclidean_inner_form_discriminant hB) =
    riemannian_linear_jacobian (@euclidean_inner_productP R m) hC m F.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
have hDet := positive_norm_factor_det_positive hL.
have hInverse := euclidean_det_inverse hLI.
have hAbs : `|euclidean_det I|*euclidean_det L = 1.
  rewrite -[euclidean_det L](ger0_norm (ltW hDet)) -normrM hInverse normr1; by [].
have hMap : hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I)) =
    hom_comp (hom_comp (hom_of_linear M) F) (hom_of_linear I).
  apply: hom_ext=> x; by [].
rewrite -(positive_norm_factor_discriminant hL) hCoordinates hMap
  euclidean_top_middle_jacobian_compose euclidean_linear_jacobian_determinant.
have hDetI : euclidean_det (hom_as_linear (hom_of_linear I)) = euclidean_det I.
  apply: det_ext=> x; by [].
rewrite hDetI -mulrA hAbs mulr1.
exact (esym (@riemannian_jacobian_target_coordinates R m n C hC M m F hM)).
Qed.
