(** Federer (1969), 3.2.46, pp. 281–282: the actual
    volume density sqrt(discr g) is continuous. Coefficients,
    the finite determinant polynomial and the proved scalar
    square-root continuity suffice; no frame field is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module
  fingroup perm.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric RealMetricBackground RiemannianTensorUP RiemannianTensorSpeedContinuity
  PositiveNormFactorDiscriminant EuclideanDiscriminantPolynomial InversionCount
  SignedSquareRootUP SignedSquareRootSealed SignedSquareRootContinuity
  RiemannianVolumeDensity PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_discriminant_along_continuous_map]:
    continuity of the original discriminant along an actual
    map into A, supporting 3.2.46, pp. 281–282. Local inner-
    product proofs disappear from its public polynomial value. *)
Lemma riemannian_discriminant_along_continuous_map (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (X : topologicalType) (p : X -> inner_metric_space (@euclidean_inner_productP R n))
    (hA : forall x, A (p x)) :
  continuous p ->
  continuous (fun x=>(euclidean_inner_form_discriminant (riemannian_tensor_inner hg (hA x))
    : real_line_metric R)).
Proof.
move=> hp.
have hFormula : (fun x=>(euclidean_inner_form_discriminant (riemannian_tensor_inner hg (hA x))
    : real_line_metric R)) =
    (fun x=>(\sum_(sigma : 'S_n) FedererPermutation.index R sigma *
      \prod_(i < n) g (p x) (@coordinate_basis R n i) (@coordinate_basis R n (sigma i))
      : real_line_metric R)).
  apply: funext=> x; exact: euclidean_inner_discriminant_polynomial.
rewrite hFormula; apply: continuous_big; first exact: add_continuous.
move=> sigma _ x; apply: (@continuousM R X); first exact: cst_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _; exact (@riemannian_coefficient_along_continuous_map R n A g hg X p
  (@coordinate_basis R n i) (@coordinate_basis R n (sigma i)) hp hA).
Qed.

(** Source for [riemannian_volume_density_along_continuous_map]:
    continuity of sqrt(discr g) itself on the original chart,
    supporting the measure derivative in 3.2.46, p. 281.
    The displayed function agrees with the sealed partial
    density at every original point. *)
Theorem riemannian_volume_density_along_continuous_map (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (X : topologicalType) (p : X -> inner_metric_space (@euclidean_inner_productP R n))
    (hA : forall x, A (p x)) :
  continuous p ->
  continuous (fun x=>(Num.sqrt
    (euclidean_inner_form_discriminant (riemannian_tensor_inner hg (hA x)))
    : real_line_metric R)).
Proof.
move=> hp.
have hDiscr := @riemannian_discriminant_along_continuous_map R n A g hg X p hA hp.
have hFormula : (fun x=>(Num.sqrt
    (euclidean_inner_form_discriminant (riemannian_tensor_inner hg (hA x)))
    : real_line_metric R)) =
    (fun x=>SignedSquareRoot.value
      (euclidean_inner_form_discriminant (riemannian_tensor_inner hg (hA x)))).
  apply: funext=> x; exact: esym (signed_square_root_nonnegative (SignedSquareRoot.laws R)
    (ltW (euclidean_inner_discriminant_positive (riemannian_tensor_inner hg (hA x))))).
rewrite hFormula=> x; exact: continuous_comp (hDiscr x) (@signed_root_continuous R _).
Qed.
