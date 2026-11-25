(** Federer (1969), 3.2.13, p. 250: the
    norm map, its differential away from zero,
    its unit Lipschitz bound and its unit normal Jacobian.
    These facts supply the actual coarea data for polar integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities InnerMetric InnerNormDifferential
  EuclideanOneCoordinate EuclideanOneNormDifferential ScalarEuclideanDifferentialTarget
  NormDifferentialUP LipschitzUP EuclideanLinearJacobian EuclideanRectangularAdjoint
  CoareaLinearDuality AdjointLaws CoordinateProjection InnerNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_radial_norm]: f(x)=|x|
    at the start of Federer 3.2.13, p. 250,
    represented in R^1 for the coarea interface. *)
Definition euclidean_radial_norm (R:realType) m
    (x:inner_metric_space (@euclidean_inner_productP R m)):
    inner_metric_space (@euclidean_inner_productP R 1):=
  euclidean_one_embed (inner_norm (@euclidean_inner_productP R m) x).

(** Source for [euclidean_radial_gradient]: the prescribed
    differential v mapped to (x dot v)/|x|,
    Federer 3.2.13, p. 250. The unit-Jacobian
    theorem below requires x nonzero. *)
Definition euclidean_radial_gradient (R:realType) m (x:R_n R m):
    Hom (R_n R m) (R_n R 1):=
  scalar_euclidean_target_hom (inner_norm_gradient (@euclidean_inner_productP R m) x).

(** Source for [euclidean_radial_differential]: the actual
    differential of f(x)=|x| for x nonzero in
    Federer 3.2.13, p. 250, proved from
    the inner-product quadratic remainder. *)
Lemma euclidean_radial_differential (R:realType) m (x:R_n R m):
  x!= 0 ->has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R 1)) setT
    (@euclidean_radial_norm R m) x (euclidean_radial_gradient x).
Proof.
move=>hx; apply:scalar_euclidean_target_differential.
exact:inner_norm_differential hx.
Qed.

(** Source for [euclidean_radial_unit_lipschitz]: Lip(f)<= 1
    for f(x)=|x| used to apply coarea in
    Federer 3.2.13, p. 250. The bound
    includes the origin and every natural source dimension. *)
Lemma euclidean_radial_unit_lipschitz (R:realType) m:
  is_metric_lipschitz_bound setT (@euclidean_radial_norm R m) 1.
Proof.
split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE mul1r euclidean_one_norm_coordinate.
change (`|(euclidean_one_embed (inner_norm (@euclidean_inner_productP R m) x)-
  euclidean_one_embed (inner_norm (@euclidean_inner_productP R m) y)) ord0|
  <=inner_norm (@euclidean_inner_productP R m) (x-y)).
rewrite /euclidean_one_embed !ffunE; exact:inner_norm_reverse_triangle.
Qed.

(** Source for [euclidean_radial_adjoint_unit]: the
    adjoint of the radial differential sends the unit
    scalar vector to x/|x|, supporting J_1 f= 1
    in Federer 3.2.13, p. 250. *)
Lemma euclidean_radial_adjoint_unit (R:realType) m (x:R_n R m):
  euclidean_rectangular_adjoint (euclidean_radial_gradient x) (@coordinate_basis R 1 ord0)=
    inner_normalize (@euclidean_inner_productP R m) x.
Proof.
apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>v.
rewrite euclidean_rectangular_adjoint_pairing euclidean_inner_basis.
change (euclidean_one_embed
    ((inner_norm (@euclidean_inner_productP R m) x)^-1*euclidean_inner_product x v) ord0=
  euclidean_inner_product v (inner_normalize (@euclidean_inner_productP R m) x)).
rewrite /euclidean_one_embed ffunE /inner_normalize
  (bilZr (inner_bilinear (@euclidean_inner_productP R m))).
by rewrite (inner_symmetric (@euclidean_inner_productP R m) v x).
Qed.

(** Source for [euclidean_radial_jacobian_one]: J_1 f(x)= 1
    for x nonzero, Federer 3.2.13, p. 250.
    The actual target-degree Jacobian is computed through
    adjoint duality and the norm of x/|x|. *)
Lemma euclidean_radial_jacobian_one (R:realType) m (x:R_n R m):
  x!= 0 ->euclidean_linear_jacobian 1 (euclidean_radial_gradient x)= 1.
Proof.
move=>hx; rewrite euclidean_target_jacobian_adjoint euclidean_one_linear_jacobian
  euclidean_radial_adjoint_unit; exact:inner_normalize_norm hx.
Qed.
