(** Supporting Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    a germ with zero centre value factors as
    the sum of its pointed coordinates times its
    actual analytic radial quotients. The proof uses
    the original Taylor and Leibniz laws. Every
    coordinate representative is a local witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HolomorphicGermDirectionalJetValue Hom RealNormUP LinearBasis FiniteDualDimension
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermJetsSealed HolomorphicGermDirectionalCoefficient
  HolomorphicGermDirectionalArithmetic HolomorphicGermDirectionalInjective HolomorphicRadialQuotientSealed
  HolomorphicRadialCoefficientSum PointedHolomorphicFunctionalGermProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_hadamard_factorisation]: a
    finite basis gives an actual coordinate factorisation
    of each original vanishing germ. This expands
    Taylor's formula from 3.1.24, pp. 238–239,
    in the ideal-closedness proof for 3.4.8(5), p. 328.
    No factorisation or vanishing-to-power conclusion
    is supplied as a premise. *)
Theorem holomorphic_hadamard_factorisation (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) a n (b:'I_n->X) (hb:is_basis b)
  (f:'I_n->@holomorphic_representative_type R X NX (complex_norm_real hNX) a)
  (alpha:[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)]):
  (forall j x,holomorphic_representative_value (f j) x = dual_basis hb j (x-a)) ->
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a 0%N alpha = 0 ->
  alpha = \sum_(j<n) (holomorphic_germ (f j):@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*
    (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)).
Proof.
move=>hF hZero.
apply:(@holomorphic_germ_directional_coefficients_injective R X NX hNX a)=>k v.
rewrite (@holomorphic_germ_directional_sum R X NX hNX a k v (Finite.clone 'I_n _)).
case:k=>[|k].
- have hSum:(\sum_(j<n) @holomorphic_germ_directional_coefficient R X NX hNX a 0%N
      ((holomorphic_germ (f j):@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*
        (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j))) v) = 0.
    apply:big1=>j _.
    exact:(@pointed_holomorphic_functional_product_zero_coefficient R X NX hNX a (dual_basis hb j)
      (f j) (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)) v (hF j)).
  by rewrite hSum holomorphic_germ_directional_coefficient_jet_value hZero linear0 mulr0.
- have hTerm j:@holomorphic_germ_directional_coefficient R X NX hNX a k.+1
      ((holomorphic_germ (f j):@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*
        (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j))) v =
      dual_basis hb j v*@holomorphic_germ_directional_coefficient R X NX hNX a k
        (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)) v.
    exact:(@pointed_holomorphic_functional_product_successor_coefficient R X NX hNX a (dual_basis hb j)
      (f j) (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)) k v (hF j)).
  under eq_bigr do rewrite hTerm.
  exact:esym (@holomorphic_radial_coefficient_basis_sum R X NX hNX a n b hb alpha k v).
Qed.
