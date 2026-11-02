(** Federer (1969), 3.2.13, p. 250: the
    actual derivative integrand in a bounded
    square substitution is twice the completed
    Gaussian power. No default derivative is
    introduced at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground GammaSquareIntegrand EulerGammaMeasurable ScalarSquareAbsoluteContinuity
  ScalarAbsoluteContinuousArea RealCurveDerivativeUP RealCurveDerivativeIntegrands
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gamma_square_source_cutoff]: the bounded
    source Gaussian weight in the Gamma
    square substitution, Federer 3.2.13, p. 250. *)
Definition gamma_square_source_cutoff (R:realType) (s b y:R):R:=
  (if `|y|<=b then 2*gamma_square_zero_completion s y else 0)%R.

(** Source for [gamma_square_area_source_graph]: the actual
    source derivative graph for the square
    substitution is exactly the bounded Gaussian
    weight, Federer 3.2.13, p. 250.
    The completed origin value is zero for
    every s and is restored later by null invariance. *)
Lemma gamma_square_area_source_graph (R:realType) (s b:R):
  (0<b)%R ->forall y z,
  partial_function_graph (scalar_curve_area_source_integrand (fun x:R=>(x^+2)%R) `[(-b)%R,b]
    (gamma_positive_completion s)) y z <->
  partial_function_graph (real_total_integrand (gamma_square_source_cutoff s b)) y z.
Proof.
move=>hb y z; rewrite real_total_integrand_graph.
have hD:partial_function_graph (real_curve_absolute_derivative_integrand (fun x:R=>(x^+2)%R)) y
    (2*`|y|)%R%:E.
  exists (2*y)%R; split; first exact:scalar_square_actual_derivative.
  have hTwo:(0<=(2:R))%R by lra.
  by rewrite normrM (ger0_norm hTwo).
case:(pselect (`[(-b)%R,b] y))=>hy.
- have hAbs:(`|y|<=b)%R by rewrite ler_norml; exact hy.
  rewrite /scalar_curve_area_source_integrand (partial_function_zero_extension_on _ _ _ hy).
  have hValue:partial_function_graph (partial_density_product
      (partial_function_total (fun x:R=>((gamma_positive_completion s (x^+2))%:E:extended_real_line R)))
      (real_curve_absolute_derivative_integrand (fun x:R=>(x^+2)%R))) y
      (2*gamma_square_zero_completion s y)%R%:E.
    apply/partial_density_product_graph.
    exists (gamma_positive_completion s (y^+2))%:E,(2*`|y|)%R%:E; split; first by [].
    split=>//; by rewrite -EFinM gamma_square_substitution_product.
  rewrite /gamma_square_source_cutoff hAbs; split=>hz.
  + exact (partial_function_single_valued hValue hz).
  + by rewrite -hz.
- have hNot:~~(`|y|<=b)%R by apply/negP=>h; apply:hy; by rewrite /= in_itv /= -ler_norml.
  rewrite /scalar_curve_area_source_integrand (partial_function_zero_extension_off _ _ _ hy)
    /gamma_square_source_cutoff (negbTE hNot).
  split=>hz; by symmetry.
Qed.
