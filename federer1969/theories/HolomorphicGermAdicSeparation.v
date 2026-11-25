(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    actual holomorphic ideals are separated by powers of
    the actual vanishing ideal. This is an algebraic
    assertion; the finite-jet topology bridge is separate.
    The original finite-dimensional Noetherian theorem and
    centre-value unit theorem supply every algebraic premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP LinearBasis HolomorphicGermRing CommutativeIdealUP
  CommutativeIdealSealed CommutativeIdealSumLaws CommutativeIdealPowersSealed
  CommutativeIdealPowersLaws HolomorphicGermNoetherian HolomorphicVanishingIdealSealed
  HolomorphicVanishingIdealLaws IdealKrullIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_ideal_adic_separation]:
    an original germ approximated modulo every power
    of the vanishing ideal by members of an original
    ideal belongs to that ideal. This expands the
    ideal-closedness argument for 3.4.8(5), p. 328,
    using the proved Noetherian assertion of 3.4.7,
    p. 325, and the project's Krull intersection proof. *)
Theorem finite_holomorphic_ideal_adic_separation (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) n (e:'I_n->X) (he:is_basis e) a
  (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)) (hI:is_commutative_ideal I)
  (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a):
  (forall k,exists beta,I beta /\@CommutativeIdealPowers.value
    [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)]
    (@HolomorphicVanishingIdeal.value R X NX (complex_norm_real hNX) a) k (alpha-beta)) ->I alpha.
Proof.
move=>hApprox.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
pose M:=@HolomorphicVanishingIdeal.value R X NX (complex_norm_real hNX) a.
have hM:=@holomorphic_vanishing_ideal_is_ideal R X NX (complex_norm_real hNX) a.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R X NX hNX n e a he.
apply:(@ideal_krull_intersection_modulo G M I hNoetherian hM hI
  (@holomorphic_vanishing_one_minus_unit R X NX (complex_norm_real hNX) a) alpha).1=>k.
have [beta [hBeta hDifference]]:=hApprox k.
apply/(@commutative_ideal_sum_membership G I (@CommutativeIdealPowers.value G M k)
  hI (@commutative_ideal_power_is_ideal G M k) alpha).
exists beta,(alpha-beta);split=>//;split=>//.
by rewrite addrC subrK.
Qed.
