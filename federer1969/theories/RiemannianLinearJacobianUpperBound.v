(** Federer (1969), 1.7.6, pp. 33–34:
    vector norm bounds control the target-degree exterior
    Jacobian. Frozen local isometries transport the
    actual bound needed for the signed coarea extension
    of 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerProductUP PositiveSymmetricNormFactor RiemannianLinearJacobian
  EuclideanLinearJacobian EuclideanRectangularAdjoint CoareaLinearDuality
  CoareaAdjointBound LinearJacobianSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_target_linear_jacobian_bound]:
    J_n D<=C^n from the actual homogeneous vector
    bound in the two original metric forms, supporting
    3.2.46, p. 282, by 1.7.6,
    pp. 33–34. Singular D, C=0 and
    target dimension zero are retained without choosing
    a global field of isometries. *)
Lemma riemannian_target_linear_jacobian_bound (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B)
    (hC : @is_inner_product R (R_n R n) C)
    (D : Hom (R_n R m) (R_n R n)) (bound : R) :
  0<=bound -> (forall v, inner_norm hC (D v)<=bound*inner_norm hB v) ->
  riemannian_linear_jacobian hB hC n D<=bound^+n.
Proof.
move=> hBound hVectors.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
pose F := hom_comp (hom_of_linear M) (hom_comp D (hom_of_linear I)).
have hEuclidean v : inner_norm (@euclidean_inner_productP R n) (F v)<=
    bound*inner_norm (@euclidean_inner_productP R m) v.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (M (D (I v)))<=
    bound*inner_norm (@euclidean_inner_productP R m) v)).
  rewrite (positive_norm_factor_norm hM).
  have hValue := hVectors (I v).
  by rewrite -(positive_norm_factor_norm hL) hIL in hValue.
have hAdjoint := euclidean_rectangular_adjoint_bound hBound hEuclidean.
have hZero v : 0*inner_norm (@euclidean_inner_productP R n) v<=
    inner_norm (@euclidean_inner_productP R m) (euclidean_rectangular_adjoint F v).
  rewrite mul0r; exact:inner_norm_nonnegative.
have hTop := (euclidean_top_jacobian_sandwich (lexx 0) hBound hZero hAdjoint).2.
rewrite (hCoordinates n D) euclidean_target_jacobian_adjoint; exact hTop.
Qed.
