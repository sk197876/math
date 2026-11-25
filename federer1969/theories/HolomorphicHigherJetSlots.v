(** Federer (1969), 3.4.12, p. 338:
    the original holomorphic first differential implies the
    complex scalar law in every actual higher derivative
    argument. Reuse ordinary first-derivative identification,
    actual symmetry and inherited argument identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexScalarRealBounded ComplexRealLinearMap HolomorphicUP ComplexScalarSlotUP
  FamilyUpdate FiniteArgumentPermutation SymmetricScalarSlotTransfer
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst NormHigherDifferentialSymmetry
  NormHigherDifferentialUnique NormHigherArgumentLinearIdentity NormDifferentialUP
  MultilinearSuccessorArguments MultilinearSuccessorPermutation MultilinearSuccessorReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Jets.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable NY:Y->R.
Variable hNX:is_complex_norm NX.
Variable hNY:is_complex_norm NY.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNYR:=(complex_norm_real hNY).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR YR NX NY hNXR hNYR).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR YR NX NY hNXR hNYR).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k XR YR NX NY hNXR hNYR).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR YR NX NY hNXR hNYR).
Variables (A:classical_sets.set X) (f:X->Y).
Hypothesis hF:is_holomorphic hNXR hNYR A f.

(** Source for [holomorphic_higher_jet_scalar_slots]: the
    original implication that every positive higher derivative
    is complex linear in each argument, 3.4.12,
    p. 338. Only the printed first-order
    complex-linearity condition is assumed. *)
Theorem holomorphic_higher_jet_scalar_slots k a (z:Z k.+1):
  @has_norm_higher_differential R XR YR NX Z ev ZN A f k.+1 a z ->
  has_complex_scalar_slot_laws (fun u=>@ev k.+1 u z).
Proof.
elim:k a z=>[|k ih] a z hActual.
- move=>u i c x.
  have hFirst:=(@norm_higher_differential_first R XR YR NX NY hNXR hNYR
    Z ev ZN hZ A f a z).1 hActual.
  have ha:=norm_domain_interior_member hNXR (norm_differential_interior hFirst).
  have hComplex:=hF.2 a _ ha hFirst.
  rewrite (ord1 i) !one_arity_replace.
  exact:(hComplex c x).
- move=>u i c x.
  have hSymmetric:=@norm_higher_differential_symmetric R XR YR NX NY hNXR hNYR
    Z ev ZN hZ A f k.+2 a z hActual.
  have [M [hMValues hM]]:=@complex_scalar_real_bounded_exists R Y NY hNY c.
  have hPrefix v y:@ev k.+2 (@family_with k.+2 (fun _=>X) v
      (lift ord_max (ord0:'I_k.+1)) (c*:y)) z=
      M (@ev k.+2 (@family_with k.+2 (fun _=>X) v
        (lift ord_max (ord0:'I_k.+1)) y) z).
    have [w [t ->]]:=multilinear_successor_arguments_surjective v.
    rewrite -!multilinear_successor_replace_prefix.
    apply:(@norm_higher_argument_linear_identity R k.+1 XR YR NX NY hNXR hNYR
      Z ev ZN hZ M A f a z _ _ hM _ hActual t).
    move=>b q hQ;rewrite hMValues.
    exact:(ih b q hQ w ord0 c y).
  rewrite -hMValues.
  exact:(@symmetric_scalar_slot_transfer X Y k.+2 (fun v=>@ev k.+2 v z)
    (lift ord_max (ord0:'I_k.+1)) (fun y=>c*:y) M hSymmetric hPrefix u i x).
Qed.
End Jets.
