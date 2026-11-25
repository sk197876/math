(** Federer (1969), 3.4.11, p. 338:
    every original leading polynomial is analytic on
    the whole finite-dimensional source. Identify its exact
    normalized jet formula with the already proved actual
    polynomial model; do not impose coefficient bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  PolynomialFunctions NormAnalyticUP AnalyticGermUP AnalyticInitialPolynomialUP
  AnalyticNormalizedJetPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_polynomial_global_analytic]: the
    finite family's actual homogeneous polynomial equations
    are globally analytic, as required in 3.4.11,
    p. 338. Analyticity follows from the original
    polynomial formula and finite source dimension. *)
Theorem analytic_initial_polynomial_global_analytic (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (alpha:analytic_germ_space (inner_norm_real_norm hB) (0:X)) k (P:X->R):
  is_initial_analytic_germ_polynomial alpha k P ->
  @norm_analytic R X R^o (inner_norm hB) (fun t:R^o=>`|t|)
    (inner_norm_real_norm hB) (@scalar_absolute_value_norm R) setT P.
Proof.
move=>hInitial.
have [Q [_ [hAnalytic hFormula]]]:=@analytic_normalized_jet_polynomial_exists R X B hB n e he k alpha.
have hEqual:P=(fun x=>Q x).
  apply:funext=>x;by rewrite hInitial.2.2.2 hFormula.
by rewrite hEqual.
Qed.
