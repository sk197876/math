(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    every ideal in the actual finite-dimensional
    holomorphic germ ring is closed for the original
    derivative metric. The proof expands the printed
    measurability argument through actual finite jets,
    coordinate factorisation and ideal Krull intersection.
    No ideal closedness is supplied as a hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexRealBasis ComplexOrderedBases RealNormUP LinearBasis HolomorphicGermRing HolomorphicGermMetric
  HolomorphicGermJetsSealed HolomorphicGermJetDifference CommutativeIdealUP
  HolomorphicIdealClosureFiniteJets HolomorphicVanishingToIdealPower HolomorphicGermAdicSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_germ_ideal_closed]:
    an original ideal is closed in the actual
    derivative metric, expanding the measurability proof
    for 3.4.8(5), p. 328. Every closure
    member agrees with an ideal member to each
    finite order; proved coordinate factorisation gives
    approximation modulo each ideal power, and the
    proved intersection theorem gives original membership.
    All centres and finite dimensions remain. *)
Theorem finite_holomorphic_germ_ideal_closed (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) n (b:'I_n->X) (hb:is_basis b) a
  (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)):
  is_commutative_ideal I ->@closed (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a) I.
Proof.
move=>hI alpha hClosure.
apply:(@finite_holomorphic_ideal_adic_separation R X NX hNX n b hb a I hI alpha)=>k.
have [beta [hBeta hAgree]]:=@holomorphic_ideal_closure_finite_jet_agreement R X NX hNX (n+n) (ordered_real_basis b) (ordered_real_basisP hb) a
  I hI alpha hClosure k.
exists beta;split=>//.
refine (@finite_holomorphic_vanishing_to_ideal_power R X NX hNX n b hb a k _ _).
move=>i hi.
by rewrite holomorphic_germ_jet_difference (hAgree i hi) subrr.
Qed.
