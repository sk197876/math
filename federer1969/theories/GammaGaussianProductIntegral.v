(** Federer (1969), 3.2.13, p. 250: the Cartesian
    Gaussian power integral equals the product of the Gamma values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  GaussianProductIntegrand GammaSquareIntegrand EulerGamma EulerGammaGaussian EuclideanFiniteProductIntegral
  PartialFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gamma_gaussian_product_integral]: the first
    multivariate integral equality in Federer 3.2.13, p. 250,
    for every family of positive z_j. Fubini proves finite
    integrability of the multivariate function as part of the conclusion. *)
Theorem gamma_gaussian_product_integral (R:realType) m (z:'I_m->R) (hz:forall j,0<z j):
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (gaussian_product_integrand z)) (\prod_j euler_gamma (hz j))%:E.
Proof.
have h:=@euclidean_finite_product_integral R m (fun j=>gamma_square_integrand (z j))
  (fun j=>euler_gamma (hz j)) (fun j=>euler_gamma_gaussian_integral (hz j)).
apply:(measure_integral_graph_equivalent _ h)=>x y.
by rewrite !real_total_integrand_graph gaussian_product_factorization.
Qed.
