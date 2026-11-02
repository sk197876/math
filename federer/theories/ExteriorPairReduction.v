(** Federer (1969), 1.7.5, p. 32: representing two multivectors in one
    finite-dimensional subspace before applying orthonormal coordinates.
    This uses the finite-support reduction already proved for Federer 1.6.1. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier FiniteSpanSpace
  FiniteIndependence ExteriorGrading ExteriorMaps ExteriorFiniteReduction
  ExteriorSubspaceReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [exterior_pair_finite_reduction]: Federer
    1.7.5, p. 32, supporting common finite-dimensional reduction
    for two multivectors, allowing distinct degrees and arbitrary
    dimension of the ambient vector space. *)
Theorem exterior_pair_finite_reduction (R : fieldType) (V : lmodType R)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  exists n (e : 'I_n -> V) (he : finite_independent e)
    (a : exterior_power (finite_span_vect he) p)
    (b : exterior_power (finite_span_vect he) q),
    exterior_power_map (subspace_inclusion (finite_span_subspace e)) p a = x /\
    exterior_power_map (subspace_inclusion (finite_span_subspace e)) q b = y.
Proof.
have [s hs] := exterior_subspace_finite_support y.
have [n [e [he [hS [a ha]]]]] := exterior_finite_dimensional_reduction x s.
have [b hb] := hs (finite_span_subspace e) hS.
by exists n, e, he, a, b; split.
Qed.
