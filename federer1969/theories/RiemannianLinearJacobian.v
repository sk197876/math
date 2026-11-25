(** Federer (1969), 3.2.46, p. 282: Jacobians
    are computed with the actual Riemannian inner products,
    using the exterior operator norm of 1.7.6, p. 33.
    Independent norm laws precede the public value, which
    reuses the existing sealed norm interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerProductUP InnerExteriorPositivity
  ExteriorGrading ExteriorMaps ExteriorOperatorNorm OperatorNormUP
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant
  OrthogonalMaps FiniteInnerChartUP FiniteInnerExteriorJacobianChart EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_riemannian_linear_jacobian]: the kth
    exterior operator norm computed in the specified source
    and target inner products, 3.2.46, p. 282. No rank
    alternative, frame or transformation formula is a law. *)
Definition is_riemannian_linear_jacobian (R : realType) m n
    (B : R_n R m -> R_n R m -> R) (C : R_n R n -> R_n R n -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) k
    (F : Hom (R_n R m) (R_n R n)) j :=
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hB k)
    (exterior_inner_productP (euclidean_two_nonzero R) hC k)
    (exterior_power_map (hom_as_linear F) k) j.

(** Source for [riemannian_linear_jacobian]: the public
    value satisfying those independent norm laws; the
    construction is already sealed in 1.7.6. This is the
    pointwise Jacobian convention required by 3.2.46, p. 282. *)
Definition riemannian_linear_jacobian (R : realType) m n
    (B : R_n R m -> R_n R m -> R) (C : R_n R n -> R_n R n -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) k
    (F : Hom (R_n R m) (R_n R n)) :=
  exterior_operator_norm (euclidean_two_nonzero R) hB hC (@coordinate_basisP R m)
    (hom_as_linear F) k.

(** Source for [riemannian_linear_jacobian_laws]: the
    actual value satisfies the independent exterior-norm
    laws, supporting 3.2.46, p. 282. *)
Lemma riemannian_linear_jacobian_laws (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C) k F :
  is_riemannian_linear_jacobian hB hC k F (riemannian_linear_jacobian hB hC k F).
Proof. exact: exterior_operator_normP. Qed.

(** Source for [riemannian_linear_jacobian_nonnegative]:
    the actual Riemannian Jacobian is nonnegative, supporting
    3.2.46, p. 282, also for singular maps and degree zero. *)
Lemma riemannian_linear_jacobian_nonnegative (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C) k F :
  0<=riemannian_linear_jacobian hB hC k F.
Proof. exact: operator_norm_nonnegative (riemannian_linear_jacobian_laws hB hC k F). Qed.

(** Source for [riemannian_linear_jacobian_coordinates]:
    frozen local linear isometries reduce the actual Riemannian
    Jacobian to the original Euclidean Jacobian of M F L^{-1},
    precisely the coordinate procedure in 3.2.46, p. 282.
    The inverse is local; all degrees share that inverse. *)
Theorem riemannian_linear_jacobian_coordinates (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C)
    (L : {linear R_n R m -> R_n R m}) (M : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L -> is_positive_symmetric_norm_factor hC M ->
  exists I : {linear R_n R m -> R_n R m}, cancel L I /\ cancel I L /\
    forall k (F : Hom (R_n R m) (R_n R n)),
      riemannian_linear_jacobian hB hC k F =
      euclidean_linear_jacobian k (hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I))).
Proof.
move=> hL hM.
have [I [hLI hIL]] := euclidean_linear_inverse (positive_norm_factor_injective hL).
have hChart : is_finite_inner_chart B (hom_of_linear I) (hom_of_linear L).
  constructor.
  - exact hIL.
  - exact hLI.
  - move=> x y; rewrite -(positive_norm_factor_pair hL) !hIL; by [].
have hIsometry : is_orthogonal_map C (@euclidean_inner_product R n) M.
  exact: positive_norm_factor_pair hM.
exists I; split; first exact hLI; split; first exact hIL.
move=> k F; apply: esym.
exact (@finite_inner_chart_exterior_jacobian R (R_n R m) (R_n R n) B C hB hC
  m n (hom_of_linear I) (hom_of_linear L) (hom_of_linear M) F k
  (riemannian_linear_jacobian hB hC k F) hChart hIsometry
  (riemannian_linear_jacobian_laws hB hC k F)).
Qed.

(** Source for [riemannian_linear_jacobian_zero_degree]:
    the actual zeroth Jacobian is one, retaining the empty
    exterior product and positive zero-dimensional atom in
    3.2.46, p. 282. *)
Lemma riemannian_linear_jacobian_zero_degree (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C) F :
  riemannian_linear_jacobian hB hC 0 F = 1.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [_ [_ hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
rewrite hCoordinates; exact: euclidean_linear_jacobian_zero_degree.
Qed.
