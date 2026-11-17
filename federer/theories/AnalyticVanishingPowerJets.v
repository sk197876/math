(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the actual vanishing-ideal powers agree exactly with finite
    original jet vanishing. One direction uses the existing
    Hadamard factorisation; the other uses the actual Leibniz bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP LinearBasis AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermRingLaws AnalyticGermJetsSealed AnalyticGermValueSealed
  AnalyticGermZerothVanishing AnalyticVanishingIdealSealed AnalyticVanishingJetProduct
  AnalyticVanishingJetIdeal AnalyticVanishingToIdealPower CommutativeIdealUP
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  CommutativeIdealProductSealed CommutativeIdealProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Powers.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation M:=(@AnalyticVanishingIdeal.value R X NX hNX a).

(** Source for [analytic_vanishing_ideal_first_jet]: supporting
    order-one connection for Federer 3.4.8(5), p. 328. Membership
    in the original centre-vanishing ideal is actual zeroth-jet
    vanishing, by the already proved representative equation. *)
Lemma analytic_vanishing_ideal_first_jet (alpha:G):M alpha ->
  analytic_germ_jets_vanish_below 1%N alpha.
Proof.
move=>hM k hk.
have hK:k = 0%N by apply/eqP;by rewrite -leqn0 -ltnS.
subst k.
have hValue:=(@AnalyticVanishingIdeal.laws R X NX hNX a alpha).1 hM.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite -hf;apply:(@analytic_germ_zeroth_vanishing R X NX hNX a f).1.
by rewrite -(@AnalyticGermValue.laws R X NX hNX a f) hf.
Qed.

(** Source for [analytic_vanishing_power_jets]: supporting
    original ideal-power implication for Federer 3.4.8(5), p. 328.
    A germ in the qth centre-vanishing ideal power has every actual
    derivative below q zero; arbitrary original normed sources remain. *)
Theorem analytic_vanishing_power_jets q alpha:
  @CommutativeIdealPowers.value G M q alpha ->
    analytic_germ_jets_vanish_below q alpha.
Proof.
elim:q alpha=>[|q ih] alpha hAlpha.
- by move=>k;rewrite ltn0.
- have hContain:@CommutativeIdealProduct.value G M
      (@CommutativeIdealPowers.value G M q) `<=`
      @analytic_germ_jets_vanish_below R X NX hNX a q.+1.
    apply:commutative_ideal_product_minimal;first exact:analytic_vanishing_jet_is_ideal.
    move=>beta gamma hB hC.
    have hh:=@analytic_product_vanishing_jets R X NX hNX a 1%N q beta gamma
      (analytic_vanishing_ideal_first_jet hB) (ih gamma hC).
    by rewrite add1n in hh.
  apply:hContain;move:hAlpha;by rewrite commutative_ideal_power_successorE.
Qed.

(** Source for [finite_analytic_vanishing_power_jet_equivalence]:
    exact original finite-jet and ideal-power identification supporting
    Federer 3.4.8(5), p. 328. Reuse the existing finite-dimensional
    Hadamard connection for the reverse implication. Zero source
    dimension and zero order are included. *)
Theorem finite_analytic_vanishing_power_jet_equivalence n (e:'I_n->X)
    (he:is_basis e) q alpha:
  @CommutativeIdealPowers.value G M q alpha <->
    analytic_germ_jets_vanish_below q alpha.
Proof.
split;first exact:analytic_vanishing_power_jets.
exact:(@finite_analytic_vanishing_to_ideal_power R X NX hNX n e he a q alpha).
Qed.
End Powers.
