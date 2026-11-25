(** Federer (1969), 1.7.12, pp. 36-37: the second trace identity, obtained
    exactly as the book indicates by applying the first identity to
    f+adjoint(f). Trace invariance under adjoints and cyclic permutation
    simplifies the four composition terms. The local erratum has no
    correction to these pages. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AdjointUP AdjointSquareTrace
  ExteriorTwoTrace TraceDefinition TraceCyclic ExteriorMaps ExteriorGrading
  FiniteExteriorPowers ExteriorIndices LinearBasis Hom Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_two_adjoint_trace]: Federer 1.7.12,
    p. 36, second display: trace(exterior_2(f+adjoint(f))) equals
    twice trace(f)^2 minus trace(f composed with f) and
    trace(adjoint(f) composed with f). The proof on p. 37 applies
    the first formula to the sum. Dimension zero is included. *)
Theorem exterior_two_adjoint_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (f a : Hom V V)
    (ha : is_adjoint B B (hom_as_linear f) (hom_as_linear a)) :
  @trace_Hom R h2 (exterior_power V 2) (Finite.clone (Lambda n 2) _)
    (@finite_e_lambda R n V e 2) (finite_e_lambda_basis he h2 2)
    (hom_of_linear (exterior_power_map (hom_as_linear (f+a)) 2)) =
  (2 : R) * (@trace_Hom R h2 V (Finite.clone 'I_n _) e he f : R)^+2 -
    @trace_Hom R h2 V (Finite.clone 'I_n _) e he (hom_comp f f) -
    @trace_Hom R h2 V (Finite.clone 'I_n _) e he (hom_comp a f).
Proof.
have hh := @exterior_two_trace R h2 V n e he (f+a).
rewrite (bilDl (@hom_comp_bilinear R V V V))
  !(bilDr (@hom_comp_bilinear R V V V)) !(linearD (@trace_Hom R h2 V (Finite.clone 'I_n _) e he))
  (@adjoint_hom_trace R h2 V B hB n e he f a ha)
  (@adjoint_square_trace R h2 V B hB n e he f a ha)
  (@trace_cyclic R h2 V (Finite.clone 'I_n _) e he f a)
  double_trace_scalar_identity in hh.
exact (mulfI h2 hh).
Qed.
