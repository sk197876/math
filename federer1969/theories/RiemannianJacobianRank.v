(** Federer (1969), 3.2.46, p. 282: the
    area/coarea extension uses the same actual differential
    rank alternatives, with Jacobians computed in the given
    Riemannian inner products. These supporting identities
    follow from 1.7.6, pp. 33–34, by local linear isometries. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP EuclideanLinearMaps ExteriorDeterminant EuclideanLinearJacobian
  CoareaLinearDuality PositiveSymmetricNormFactor PositiveNormFactorDiscriminant
  RiemannianLinearJacobian RiemannianJacobianVolumeFactor TopMiddleJacobianComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_area_jacobian_positive_iff_injective]:
    positivity of the actual source-degree Riemannian Jacobian
    is equivalent to injectivity of the original linear map,
    supporting 3.2.46, p. 282, and the rank decomposition
    of 3.2.3, p. 243. Includes source dimension zero. *)
Lemma riemannian_area_jacobian_positive_iff_injective (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C)
    (F : Hom (R_n R m) (R_n R n)) :
  0<riemannian_linear_jacobian hB hC m F <-> injective F.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
rewrite hCoordinates euclidean_linear_jacobian_top_positive.
split.
- move=> hInj x y hEq.
  have h : hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I)) (L x)=
      hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I)) (L y).
    change (M (F (I (L x)))=M (F (I (L y)))); by rewrite !hLI hEq.
  have hXY := hInj _ _ h.
  exact: (positive_norm_factor_injective hL) hXY.
- move=> hInj x y hEq.
  have h1 : F (I x)=F (I y) := (positive_norm_factor_injective hM) _ _ hEq.
  have h2 : I x=I y := hInj _ _ h1.
  exact: (can_inj hIL) h2.
Qed.

(** Source for [riemannian_coarea_jacobian_positive_iff_surjective]:
    positivity of the target-degree Riemannian Jacobian is
    equivalent to surjectivity of the original differential,
    supporting 3.2.46, p. 282, and 3.2.11, p. 249.
    Includes target dimension zero and every singular map. *)
Lemma riemannian_coarea_jacobian_positive_iff_surjective (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C)
    (F : Hom (R_n R m) (R_n R n)) :
  0<riemannian_linear_jacobian hB hC n F <-> forall y, exists x, F x=y.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
have [N [hMN hNM]] := euclidean_linear_inverse (positive_norm_factor_injective hM).
rewrite hCoordinates euclidean_target_jacobian_positive_iff_surjective.
split.
- move=> hOnto y.
  have [x hx] := hOnto (M y).
  exists (I x); exact: (positive_norm_factor_injective hM) _ _ hx.
- move=> hOnto y.
  have [x hx] := hOnto (N y).
  exists (L x); change (M (F (I (L x)))=y).
  by rewrite hLI hx hNM.
Qed.

(** Source for [riemannian_square_jacobian_volume_factor]:
    the exact Riemannian change-of-variables factor of
    3.2.46, p. 282: J_{B,C}(F) sqrt(discr B)
    equals sqrt(discr C) times |det F|. This is
    proved for singular maps too, including dimension zero. *)
Theorem riemannian_square_jacobian_volume_factor (R : realType) n B C
    (hB : @is_inner_product R (R_n R n) B) (hC : @is_inner_product R (R_n R n) C)
    (F : Hom (R_n R n) (R_n R n)) :
  riemannian_linear_jacobian hB hC n F * Num.sqrt (euclidean_inner_form_discriminant hB) =
    Num.sqrt (euclidean_inner_form_discriminant hC)*`|euclidean_det (hom_as_linear F)|.
Proof.
have [M hM] := positive_symmetric_norm_factor_exists hC.
rewrite riemannian_area_jacobian_volume_factor
  (@riemannian_jacobian_target_coordinates R n n C hC M n F hM)
  euclidean_top_middle_jacobian_compose !euclidean_linear_jacobian_determinant.
have hDetM : euclidean_det (hom_as_linear (hom_of_linear M))=euclidean_det M.
  apply: det_ext=> x; by [].
rewrite hDetM (ger0_norm (ltW (positive_norm_factor_det_positive hM))).
by rewrite (positive_norm_factor_discriminant hM).
Qed.
