(** Federer (1969), 3.4.6, pp. 321–324: actual
    scalar and planar regressions, with the original
    zero-dimensional source boundary retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Weierstrass RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness AnalyticGermUP WeierstrassRegularUP WeierstrassRegularProperties.
From FedererTests Require Import WeierstrassScalarExamples WeierstrassPlanarExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_zero_source_regression]: the
    printed positive-order regularity cannot hold in
    the actual zero-dimensional source, testing 3.4.6,
    p. 321. No positive-dimension assumption is
    silently added to the original theorem. *)
Example weierstrass_zero_source_regression (R:realType):
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 0) in
  forall (Phi:analytic_germ_space hN (0:R_n R 0)) k v,
    ~is_weierstrass_regular_germ Phi k v.
Proof.
move=>hN Phi k v hRegular.
have hNonzero:=@weierstrass_regular_direction_nonzero R (R_n R 0) _ hN Phi k v hRegular.
exact:hNonzero (coordinate_zero v).
Qed.
