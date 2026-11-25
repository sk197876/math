(** Concrete boundary regressions for the corrected coefficient assertion
    in Federer 1.4.4, p. 20. The scalar line has a noninjective Omega with
    two-dimensional coefficients; the zero source retains its injective
    counterexample. These examples are additional project checks. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CoefficientCoordinates
  OmegaConstruction CoefficientCounterexample ZeroDimensionalCoefficients
  CoefficientNoninjectivity FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Examples.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation W := (coefficient_pair_algebra K).

(** Source for [scalar_line_coefficient_pair_noninjective]: regression
    for the corrected noninjectivity assertion in Federer 1.4.4, p. 20.
    The source is the actual scalar line and W=K times K. A singleton
    coefficient-unit basis would represent (1,0) as (c,c), an impossibility. *)
Theorem scalar_line_coefficient_pair_noninjective :
    ~ injective (Omega_W h2 K^o (@coefficient_pair_commutative K)).
Proof.
move=> hi.
have hb := @Omega_W_injective_requires_coefficient_line K h2 K^o W
  (@coefficient_pair_commutative K) 1 (oner_neq0 K) hi.
have [c hc] : exists c : K, (1,0) = c *: (alg_one W).
  exists (free_eval ord0 (basis_coordinates hb (1,0))).
  have h := basis_coordinatesK hb (1,0).
  rewrite basis_synthesis_finiteE big_ord1 in h.
  exact: esym h.
change ((1,0) = (c*1,c*1)) in hc; rewrite !mulr1 in hc.
have h1 := congr1 (@fst K K) hc.
have h0 := congr1 (@snd K K) hc.
change (1=c) in h1; change (0=c) in h0.
by move: (eq_trans h1 (esym h0)) => /eqP; rewrite oner_eq0.
Qed.

(** Source for [zero_source_coefficient_pair_injective]: regression for
    the zero-source exception to Federer 1.4.4, p. 20. Reuse the checked
    concrete counterexample; it verifies why the corrected general theorem
    explicitly requires a nonzero source. *)
Theorem zero_source_coefficient_pair_injective :
    injective (Omega_W h2 (coordinate_space K 0)
      (@coefficient_pair_commutative K)).
Proof. exact: zero_domain_Omega_pair_injective. Qed.
End Examples.
