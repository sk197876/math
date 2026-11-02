(** Federer (1969), 1.7.4, pp. 30-31: O*(n,m) and the coordinate projection
    p_lambda. The coordinate formula is part of this named map's
    specification; its orthogonal-adjoint witness is constructed from the
    basis laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP OrthogonalEuclidean OrthogonalMaps
  AdjointUP AdjointLaws AdjointCriteria ProjectionCriteria
  ExteriorIndices LambdaPermutation LinearBasis BasisInterpolation
  BilinearPrecompose BilinearBasisExt TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [O_star]: Federer 1.7.4, pp. 30-31,
    O*(n,m) is the set of adjoints of members of O(n,m), hence
    projections from R^n onto R^m. Dimensions zero are included. *)
Definition O_star (R : realFieldType) n m :
    set {linear R_n R n -> R_n R m} :=
  [set p | exists f : {linear R_n R m -> R_n R n},
    @FedererOrthogonal.O R n m f /\
    is_adjoint (@euclidean_inner_product R m) (@euclidean_inner_product R n) f p].

(** Source for [O_star_projection]: Federer 1.7.4, pp. 30-31,
    this is exactly the set of orthogonal projections between
    the indicated Euclidean spaces. *)
Lemma O_star_projection (R : realFieldType) n m
    (p : {linear R_n R n -> R_n R m}) :
  O_star p <-> is_orthogonal_projection
    (@euclidean_inner_product R n) (@euclidean_inner_product R m) p.
Proof. by []. Qed.

(** Source for [euclidean_inner_basis]: Federer 1.7.4,
    p. 31, supporting calculation for coordinate projections:
    the inner product with the i-th standard basis vector is x_i. *)
Lemma euclidean_inner_basis (R : realFieldType) n (x : R_n R n) i :
  euclidean_inner_product x (@coordinate_basis R n i) = x i.
Proof.
rewrite /euclidean_inner_product (bigD1 i) //= /coordinate_basis ffunE eqxx mulr1.
have hz : (\sum_(j : 'I_n | j != i) x j * @coordinate_basis R n i j) = 0.
  apply: big1 => j hj; rewrite /coordinate_basis ffunE.
  by rewrite (negbTE hj) mulr0.
by rewrite hz addr0.
Qed.
Section Projection.
Variable R : realFieldType.
Variables n m : nat.
Variable lambda : Lambda n m.
Local Notation l := (tnth (val lambda)).

(** Source for [coordinate_projection]: Federer 1.7.4,
    p. 31, displayed formula: p_lambda(x)_i=x_(lambda(i)). *)
Definition coordinate_projection (x : R_n R n) : R_n R m := [ffun i => x (l i)].

(** Source for [coordinate_projection_linear]: Federer 1.7.4,
    p. 31, supporting linearity of the displayed coordinate map. *)
Lemma coordinate_projection_linear : linear coordinate_projection.
Proof. by move=> a x y; apply/ffunP=> i; rewrite /coordinate_projection !ffunE. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R n) (R_n R m)
  *:%R coordinate_projection coordinate_projection_linear.

(** Source for [coordinate_projectionE]: Federer 1.7.4,
    p. 31, the i-th selected coordinate of p_lambda(x). *)
Lemma coordinate_projectionE x i : coordinate_projection x i = x (l i).
Proof. exact: ffunE. Qed.

(** Source for [coordinate_injection]: Federer 1.7.4, p. 31, supporting
    adjoint witness, sending e_i to e_(lambda(i)). *)
Definition coordinate_injection :=
  basis_interpolation (@coordinate_basisP R m) (fun i => @coordinate_basis R n (l i)).

(** Source for [coordinate_projection_selected_basis]: Federer
    1.7.4, p. 31, supporting identity p_lambda(e_(lambda(i)))=e_i. *)
Lemma coordinate_projection_selected_basis i :
  coordinate_projection (@coordinate_basis R n (l i)) = @coordinate_basis R m i.
Proof.
apply/ffunP=> j; rewrite coordinate_projectionE /coordinate_basis !ffunE.
by rewrite (inj_eq (@Lambda_tnth_injective n m lambda)).
Qed.

(** Source for [coordinate_projection_injectionK]: Federer 1.7.4, p. 31,
    supporting identity p_lambda composed with its coordinate injection is
    identity. *)
Lemma coordinate_projection_injectionK : cancel coordinate_injection coordinate_projection.
Proof.
move=> x; apply: (basis_linear_ext (@coordinate_basisP R m)
  (linear_comp (GRing.Linear.clone _ _ _ _ coordinate_projection _) coordinate_injection)
  (linear_id (R_n R m))) x => i.
change (coordinate_projection (coordinate_injection (@coordinate_basis R m i)) = @coordinate_basis R m i).
by rewrite /coordinate_injection basis_interpolationE coordinate_projection_selected_basis.
Qed.

(** Source for [coordinate_projection_adjoint]: Federer 1.7.4,
    p. 31, the adjoint of p_lambda sends the i-th basis vector
    to the lambda(i)-th basis vector. *)
Lemma coordinate_projection_adjoint :
  is_adjoint (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    (GRing.Linear.clone _ _ _ _ coordinate_projection _) coordinate_injection.
Proof.
apply: (@bilinear_basis_ext R (Choice.clone 'I_n _) (Choice.clone 'I_m _)
  (R_n R n) (R_n R m) R^o (@coordinate_basis R n) (@coordinate_basis R m)
  (@coordinate_basisP R n) (@coordinate_basisP R m)).
- exact: (bilinear_linear_precompose (@euclidean_inner_bilinear R n)
    (linear_id (R_n R n)) coordinate_injection).
- exact: (bilinear_linear_precompose (@euclidean_inner_bilinear R m)
    (GRing.Linear.clone _ _ _ _ coordinate_projection _) (linear_id (R_n R m))).
- move=> i j; rewrite /coordinate_injection basis_interpolationE !euclidean_inner_basis.
  exact: esym (coordinate_projectionE _ _).
Qed.

(** Source for [coordinate_projection_orthogonal]: Federer
    1.7.4, p. 31, p_lambda belongs to O*(n,m). *)
Theorem coordinate_projection_orthogonal :
  O_star (GRing.Linear.clone _ _ _ _ coordinate_projection _).
Proof.
apply: (proj2 (@projection_iff_adjoint_right_inverse R
  (R_n R n) (R_n R m) (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (GRing.Linear.clone _ _ _ _ coordinate_projection _) coordinate_injection
  coordinate_projection_adjoint)).
exact: coordinate_projection_injectionK.
Qed.
End Projection.
