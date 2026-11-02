(** Federer (1969), 1.7.12, pp. 36-37: the first displayed trace identity.
    The book's degree-two coefficient is evaluated through the divided-power
    identity already proved from 1.4.5, rather than by introducing a second
    polynomial expansion. This documents the proof departure while retaining
    the same degree-two algebra. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TraceGammaProduct TraceDefinition TracePower
  DividedPowers AlgebraUP AlgebraPowers GammaPower ExteriorMaps ExteriorGrading
  FiniteExteriorPowers ExteriorIndices LinearBasis Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_two_trace]: Federer 1.7.12,
    p. 36, first display: twice the trace of exterior_2(f)
    equals trace(f)^2 minus trace(f composed with f). The proof
    is valid over any field with 2 nonzero and in dimensions zero
    and one, where the second exterior power vanishes. *)
Theorem exterior_two_trace (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e) (f : Hom V V) :
  (2 : K) * @trace_Hom K h2 (exterior_power V 2) (Finite.clone (Lambda n 2) _)
    (@finite_e_lambda K n V e 2) (finite_e_lambda_basis he h2 2)
    (hom_of_linear (exterior_power_map (hom_as_linear f) 2)) =
  (@trace_Hom K h2 V (Finite.clone 'I_n _) e he f : K)^+2 -
    @trace_Hom K h2 V (Finite.clone 'I_n _) e he (hom_comp f f).
Proof.
have hh := congr1 (trace h2 V) (@Gamma_power_factorial K h2 V V n e he f 2).
rewrite /AlgebraPowers.algebra_power alg_unitr linearZ trace_Gamma_power
  trace_gamma_product in hh.
change ((@trace_Hom K h2 V (Finite.clone 'I_n _) e he f : K) *
    @trace_Hom K h2 V (Finite.clone 'I_n _) e he f -
    @trace_Hom K h2 V (Finite.clone 'I_n _) e he (hom_comp f f) =
  (2 : K) * @trace_Hom K h2 (exterior_power V 2) (Finite.clone (Lambda n 2) _)
    (@finite_e_lambda K n V e 2) (finite_e_lambda_basis he h2 2)
    (hom_of_linear (exterior_power_map (hom_as_linear f) 2))) in hh.
by rewrite expr2; symmetry.
Qed.
