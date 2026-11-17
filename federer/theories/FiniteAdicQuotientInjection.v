(** Supporting Federer (1969), 3.4.8(5), p. 328:
    coefficient-linear separation and the proved adic shift inject
    original Taylor polynomials into a sufficiently deep quotient.
    Only exact original ideal-power and scalar laws are used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction CommutativeIdealUP CommutativeQuotientUP
  CommutativeIdealPowersSealed IdealPowerBlockInclusion LinearFunctionalIdealPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_adic_quotient_injection]: supporting original
    finite Taylor dimension comparison for Federer 3.4.8(5), p. 328.
    The coefficient-linear functional and actual Artin--Rees shift
    detect the original Taylor classes. Scalar-generated ideal powers
    are transported by the proved multiplier-ideal lemma. *)
Theorem finite_adic_quotient_injection (K:fieldType) (A C Q:comNzRingType)
    (constants:{rmorphism K->A}) (phi:{rmorphism A->C}) (scalar:{rmorphism K->C})
    (rho:{rmorphism C->Q}) (I:set A) (M J:set C) b r l (U:finType)
    (L:{linear [the lmodType A of ring_restricted_space phi C^o]->A^o})
    (F:A->{ffun U->K^o})
    (T:{linear {ffun U->K^o}->[the lmodType K of ring_restricted_space constants A^o]}):
  (forall c:K,phi (constants c) = scalar c) ->
  is_generated_commutative_ideal (phi @` I) J ->
  @CommutativeIdealPowers.value C M b `<=` J ->
  (forall a:A,@CommutativeIdealPowers.value A I (r+l)%N (L 1*a) ->
    @CommutativeIdealPowers.value A I l a) ->
  (forall a:A,F a = 0 <->@CommutativeIdealPowers.value A I l a) ->
  cancel T F ->
  is_commutative_ideal_quotient (@CommutativeIdealPowers.value C M (b*(r+l))%N) rho ->
  exists f:{linear {ffun U->K^o}->
    [the lmodType K of ring_restricted_space
      (GRing.RMorphism.clone K Q (rho \o scalar) _) Q^o]},injective f.
Proof.
move=>hConstants hJ hBlock hShift hKernel hSection hRho.
pose V:=[the lmodType K of {ffun U->K^o}].
pose W:=[the lmodType K of ring_restricted_space
  (GRing.RMorphism.clone K Q (rho \o scalar) _) Q^o].
pose value(c:V):=rho (phi (T c)).
have hLinear:linear (value:V->W).
  move=>a c d.
  rewrite /value linearP.
  change (rho (phi (constants a*T c+T d)) =
    rho (scalar a)*rho (phi (T c))+rho (phi (T d))).
  by rewrite !rmorphD !rmorphM hConstants.
pose f:{linear V->W}:=HB.pack value (GRing.isLinear.Build K V W *:%R value hLinear).
have hZero c:f c = 0 ->c = 0.
  move=>hC.
  have hPower:@CommutativeIdealPowers.value C M (b*(r+l))%N (phi (T c)).
    apply:(commutative_quotient_kernel hRho _).1;exact:hC.
  have hJPower:=@commutative_ideal_power_block_inclusion C M J b hBlock (r+l)%N _ hPower.
  have hFunctional:=@linear_functional_scalar_ideal_powers A C phi L I J hJ
    (r+l)%N (phi (T c)) hJPower 1.
  rewrite mul1r in hFunctional.
  have hEvaluate:L (phi (T c)) = L 1*T c.
    rewrite mulrC.
    have hh:L ((T c)*:(1:[the lmodType A of ring_restricted_space phi C^o])) =
        (T c)*:L 1 by rewrite linearZ.
    change (L (phi (T c)*1) = T c*L 1) in hh.
    by rewrite mulr1 in hh.
  rewrite hEvaluate in hFunctional.
  have hCoefficientZero:F (T c) = 0:=(hKernel _).2 (hShift _ hFunctional).
  by rewrite hSection in hCoefficientZero.
exists f=>c d hEqual.
have hDifference:f (c-d) = 0 by rewrite linearB hEqual subrr.
have hh:=hZero _ hDifference;exact:subr0_eq hh.
Qed.
