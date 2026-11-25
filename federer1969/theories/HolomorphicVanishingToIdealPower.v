(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    vanishing finite jets imply membership in the
    corresponding power of the actual vanishing ideal.
    The proof iterates actual coordinate factorisation
    and the quotient's proved order reduction. No
    formal-series ideal is substituted for the germ ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexRealBasis ComplexOrderedBases ComplexRealLinearMap HolomorphicLinear Hom RealNormUP LinearBasis FiniteDualDimension NormFiniteLinearBound
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicGermJetsSealed
  HolomorphicGermValueSealed HolomorphicVanishingIdealSealed HolomorphicVanishingIdealUP
  CommutativeIdealUP CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws PointedHolomorphicFunctionalGermExistence
  HolomorphicRadialQuotientSealed HolomorphicRadialQuotientVanishing HolomorphicHadamardFactorisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_vanishing_to_ideal_power]:
    if every actual derivative below k vanishes,
    the original holomorphic germ lies in the kth
    power of the actual centre-vanishing ideal.
    This proves the finite-jet bridge in the
    expanded closedness argument for 3.4.8(5), p. 328.
    All centres, finite dimensions, and k=0 remain. *)
Theorem finite_holomorphic_vanishing_to_ideal_power (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) n (b:'I_n->X) (hb:is_basis b) a:
  forall k (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a),
  (forall i,(i<k)%N ->@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha = 0) ->
  @CommutativeIdealPowers.value [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)]
    (@HolomorphicVanishingIdeal.value R X NX (complex_norm_real hNX) a) k alpha.
Proof.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
pose M:=@HolomorphicVanishingIdeal.value R X NX (complex_norm_real hNX) a.
pose P:=@CommutativeIdealPowers.value G M.
elim=>[|k ih] alpha hZero.
- rewrite commutative_ideal_power_zeroE;exact:Logic.I.
- have hEach j:exists f:@holomorphic_representative_type R X NX (complex_norm_real hNX) a,
      forall x,holomorphic_representative_value f x = dual_basis hb j (x-a).
    apply:(@pointed_holomorphic_functional_representative_exists R X NX hNX a (dual_basis hb j)).
    exact:(@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
      (complex_norm_real hNX) (@complex_modulus_real_norm R) (n+n)
      (ordered_real_basis b) (ordered_real_basisP hb) (complex_hom_real (dual_basis hb j))).
  have [f hF]:=choice hEach.
  have hFactor:=@holomorphic_hadamard_factorisation R X NX hNX a n b hb f alpha hF
    (hZero 0%N (ltn0Sn k)).
  rewrite hFactor.
  apply:(big_ind (P k.+1)).
  + exact:commutative_ideal_zero (@commutative_ideal_power_is_ideal G M k.+1).
  + move=>u v hu hv;exact:(@commutative_ideal_add G (P k.+1)
      (@commutative_ideal_power_is_ideal G M k.+1) u v hu hv).
  + move=>j _;rewrite /P commutative_ideal_power_successorE.
    apply:commutative_ideal_product_contains.
    * apply/(@HolomorphicVanishingIdeal.laws R X NX (complex_norm_real hNX) a (holomorphic_germ (f j))).
      by rewrite (@HolomorphicGermValue.laws R X NX (complex_norm_real hNX) a (f j)) (hF j) subrr linear0.
    * apply:ih.
      exact:(@holomorphic_radial_quotient_lowers_order R X NX hNX a alpha (b j) k hZero).
Qed.
