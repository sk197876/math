(** Supporting Federer (1969), 3.4.8(5), p. 328:
    vanishing finite jets imply membership in the
    corresponding power of the actual vanishing ideal.
    The proof iterates actual coordinate factorisation
    and the quotient's proved order reduction. No
    formal-series ideal is substituted for the germ ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension NormFiniteLinearBound
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticGermJetsSealed
  AnalyticGermValueSealed AnalyticVanishingIdealSealed AnalyticVanishingIdealUP
  CommutativeIdealUP CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws PointedFunctionalGermExistence
  AnalyticRadialQuotientSealed AnalyticRadialQuotientVanishing AnalyticHadamardFactorisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_vanishing_to_ideal_power]:
    if every actual derivative below k vanishes,
    the original analytic germ lies in the kth
    power of the actual centre-vanishing ideal.
    This proves the finite-jet bridge in the
    expanded closedness argument for 3.4.8(5), p. 328.
    All centres, finite dimensions, and k=0 remain. *)
Theorem finite_analytic_vanishing_to_ideal_power (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b) a:
  forall k (alpha:@analytic_germ_ring R X NX hNX a),
  (forall i,(i<k)%N ->@AnalyticGermJets.value R X NX hNX a i alpha = 0) ->
  @CommutativeIdealPowers.value [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]
    (@AnalyticVanishingIdeal.value R X NX hNX a) k alpha.
Proof.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose M:=@AnalyticVanishingIdeal.value R X NX hNX a.
pose P:=@CommutativeIdealPowers.value G M.
elim=>[|k ih] alpha hZero.
- rewrite commutative_ideal_power_zeroE;exact:Logic.I.
- have hEach j:exists f:@analytic_representative_type R X NX hNX a,
      forall x,analytic_representative_value f x = dual_basis hb j (x-a).
    apply:(@pointed_functional_representative_exists R X NX hNX a (dual_basis hb j)).
    exact:(@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
      (@scalar_absolute_value_norm R) n b hb (dual_basis hb j)).
  have [f hF]:=choice hEach.
  have hFactor:=@analytic_hadamard_factorisation R X NX hNX a n b hb f alpha hF
    (hZero 0%N (ltn0Sn k)).
  rewrite hFactor.
  apply:(big_ind (P k.+1)).
  + exact:commutative_ideal_zero (@commutative_ideal_power_is_ideal G M k.+1).
  + move=>u v hu hv;exact:(@commutative_ideal_add G (P k.+1)
      (@commutative_ideal_power_is_ideal G M k.+1) u v hu hv).
  + move=>j _;rewrite /P commutative_ideal_power_successorE.
    apply:commutative_ideal_product_contains.
    * apply/(@AnalyticVanishingIdeal.laws R X NX hNX a (analytic_germ (f j))).
      by rewrite (@AnalyticGermValue.laws R X NX hNX a (f j)) (hF j) subrr linear0.
    * apply:ih.
      exact:(@analytic_radial_quotient_lowers_order R X NX hNX a alpha (b j) k hZero).
Qed.
