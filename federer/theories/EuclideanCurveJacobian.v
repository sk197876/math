(** Federer (1969), 3.2.6, p. 245: the actual
    speed integrand is the one-dimensional Jacobian under
    the scalar coordinate identification. Undefined derivatives
    remain undefined on both sides. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  InnerNorm HilbertFormCompactness NormDifferentialUP NormedCurveDerivativeUP NormedCurveDerivativeIntegrands
  EuclideanOneNormDifferential EuclideanLinearJacobian Jacobian PartialFunctionUP PartialFunctionPostcomposition
  EuclideanJacobianMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_curve_linear_map]: supporting
    linear approximation h maps to h f'(a) in
    Federer 3.2.6, p. 245, by the scalar-source
    differentiation rule of 3.1.1, p. 209. *)
Definition euclidean_curve_linear_map (R:realType) n (v:R_n R n):Hom (R_n R 1) (R_n R n).
Proof.
refine (@HomMap R (R_n R 1) (R_n R n) (fun x=>x ord0*:v) _).
apply/asboolP=>c x y; rewrite !ffunE scalerDl scalerA; by [].
Defined.

(** Source for [euclidean_curve_linear_map_basis]: the
    derivative is the image of the scalar unit vector,
    supporting the factor |f'| of Federer 3.2.6, p. 245. *)
Lemma euclidean_curve_linear_map_basis (R:realType) n (v:R_n R n):
  euclidean_curve_linear_map v (@coordinate_basis R 1 ord0)=v.
Proof. by rewrite /euclidean_curve_linear_map /= /coordinate_basis ffunE eqxx scale1r. Qed.

(** Source for [euclidean_curve_jacobian_graph]: exact
    speed-Jacobian identification in Federer 3.2.6, p. 245.
    It asserts equality of actual graphs, including their
    domains, without assuming absolute continuity. *)
Theorem euclidean_curve_jacobian_graph (R:realType) n (f:R->R_n R n) a j:
  partial_function_graph (euclidean_jacobian 1 setT (fun x=>f (euclidean_one_project x)))
    (euclidean_one_embed a) j <->
  exists v:R_n R n,has_normed_curve_derivative (inner_norm (@euclidean_inner_productP R n)) f a v /\
    inner_norm (@euclidean_inner_productP R n) v=j.
Proof.
rewrite euclidean_jacobian_graph; split.
- move=>[L [hL hJ]]; exists (L (@coordinate_basis R 1 ord0)); split.
  + exact ((euclidean_one_differential_curve_iff f a L).1 hL).
  + by rewrite -euclidean_one_linear_jacobian.
- move=>[v [hv hJ]]; exists (euclidean_curve_linear_map v); split.
  + apply:(euclidean_one_differential_curve_iff f a (euclidean_curve_linear_map v)).2.
    by rewrite euclidean_curve_linear_map_basis.
  + by rewrite euclidean_one_linear_jacobian euclidean_curve_linear_map_basis.
Qed.

(** Source for [euclidean_curve_extended_jacobian_graph]: the
    same speed integrand in the extended integral carrier
    of Federer 3.2.6, p. 245. Both partial graphs
    retain exactly the points where the derivative exists. *)
Corollary euclidean_curve_extended_jacobian_graph (R:realType) n (f:R->R_n R n) a j:
  partial_function_graph (extended_euclidean_jacobian (fun x=>f (euclidean_one_project x)))
    (euclidean_one_embed a) j <->
  partial_function_graph (normed_curve_norm_derivative_integrand
    (inner_norm_real_norm (@euclidean_inner_productP R n)) f) a j.
Proof.
split.
- move=>[r [hr <-]]; have [v [hv hNorm]]:=(euclidean_curve_jacobian_graph f a r).1 hr.
  exists v; split=>//; by rewrite hNorm.
- move=>[v [hv <-]]; exists (inner_norm (@euclidean_inner_productP R n) v); split=>//.
  apply:(euclidean_curve_jacobian_graph f a _).2; by exists v.
Qed.
