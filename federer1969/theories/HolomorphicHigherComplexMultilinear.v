(** Federer (1969), 3.4.12, p. 338:
    every actual positive higher differential of an
    original holomorphic function is complex multilinear.
    The real differential graph remains the original
    recursive one, with its proved continuous evaluation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  TensorFamilyUP ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  HolomorphicUP HolomorphicHigherJetSlots ComplexMultilinearFromReal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Jets.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:is_complex_norm NX.
Variable hNY:is_complex_norm NY.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNYR:=(complex_norm_real hNY).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR YR NX NY hNXR hNYR).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR YR NX NY hNXR hNYR).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k XR YR NX NY hNXR hNYR).

(** Source for [holomorphic_higher_complex_multilinear]: the
    full original higher-derivative assertion of 3.4.12,
    p. 338. Arbitrary complex normed sources
    and targets, every positive order and all original
    argument slots remain; no higher complex-linearity premise
    is added to the holomorphic definition. *)
Theorem holomorphic_higher_complex_multilinear (A:set X) (f:X->Y) k a (z:Z k.+1):
  is_holomorphic hNXR hNYR A f ->
  @has_norm_higher_differential R XR YR NX Z ev ZN A f k.+1 a z ->
  @multilinear (ComplexScalars.C R) k.+1 (fun _=>X) Y
    (fun u=>@ev k.+1 u z).
Proof.
move=>hF hActual.
apply:complex_multilinear_from_real.
- exact:(continuous_multilinear_evaluation
    (@ContinuousMultilinear.laws R k.+1 XR YR NX NY hNXR hNYR) z).
- exact:(@holomorphic_higher_jet_scalar_slots R X Y NX NY hNX hNY A f hF k a z hActual).
Qed.
End Jets.
