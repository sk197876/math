(** Federer (1969), 3.2.46, p. 282: an
    actual frozen source inverse and target isometry
    compute the original linear Jacobian. The differential
    coordinate calculation uses 3.1.1(2), p. 210,
    and retains exact actual partial Jacobian values. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations InnerProductUP PositiveSymmetricNormFactor
  RiemannianLinearJacobian EuclideanLinearJacobian EuclideanFrozenDifferential
  EuclideanInnerProduct InnerNorm NormDifferentialUP Jacobian EuclideanTargetJacobianMeasurable
  PartialFunctionUP PartialFunctionPrecomposition ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [riemannian_linear_jacobian_given_coordinates]:
    every proved local inverse of the actual frozen
    factor gives the same Jacobian, supporting 3.2.46,
    p. 282. The result follows from uniqueness of
    an inverse and the public isometry laws, including
    singular F and the zeroth exterior degree. *)
Lemma riemannian_linear_jacobian_given_coordinates (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B)
    (hC : @is_inner_product R (R_n R n) C)
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L -> is_positive_symmetric_norm_factor hC M ->
  cancel L I -> forall k (F : Hom (R_n R m) (R_n R n)),
  riemannian_linear_jacobian hB hC k F=
    euclidean_linear_jacobian k (hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I))).
Proof.
move=> hL hM hLI k F.
have [J [hLJ [hJL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
have hInverse : hom_of_linear J=hom_of_linear I.
  apply:hom_ext=> v; change (J v=I v).
  by rewrite -{2}(hJL v) hLI.
by rewrite (hCoordinates k F) hInverse.
Qed.

(** Source for [frozen_riemannian_coarea_jacobian_graph]:
    an actual DF gives the actual partial target-degree
    Jacobian of M F L^{-1} at L(a), supporting
    3.2.46, p. 282. No derivative field,
    arbitrary Jacobian extension or noncritical-rank premise
    is assumed; the exact original domain is retained. *)
Lemma frozen_riemannian_coarea_jacobian_graph (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B)
    (hC : @is_inner_product R (R_n R n) C)
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n})
    (F : R_n R m -> R_n R n) a (D : Hom (R_n R m) (R_n R n)) :
  is_positive_symmetric_norm_factor hB L -> is_positive_symmetric_norm_factor hC M ->
  cancel L I ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) classical_sets.setT F a D ->
  partial_function_graph (partial_function_precompose L
    (extended_euclidean_target_jacobian (fun z=>M (F (I z))))) a
      (riemannian_linear_jacobian hB hC n D)%:E.
Proof.
move=> hL hM hLI hD.
pose DG := hom_comp (hom_of_linear M) (hom_comp D (hom_of_linear I)).
have hDifferential := euclidean_frozen_differential M hLI hD.
exists (riemannian_linear_jacobian hB hC n D); split; last by [].
apply:(euclidean_jacobian_graph n classical_sets.setT (fun z=>M (F (I z))) (L a) _).2.
exists DG; split; first exact hDifferential.
exact:esym (@riemannian_linear_jacobian_given_coordinates R m n B C hB hC L I M hL hM hLI n D).
Qed.
