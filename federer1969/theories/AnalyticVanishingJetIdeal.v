(** Supporting Federer (1969), 3.4.8(5), p. 328:
    exact original finite vanishing conditions are ideals.
    Use actual jet arithmetic and the existing Leibniz estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticGermSealed
  AnalyticGermJetsSealed AnalyticGermJetArithmetic AnalyticGermJetZeroNegate
  CommutativeIdealUP AnalyticVanishingJetProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_vanishing_jet_is_ideal]: supporting
    original finite-jet filtration for Federer 3.4.8(5), p. 328.
    The germs whose actual derivatives below q vanish form an ideal;
    its definition includes no ideal or power assertion. *)
Theorem analytic_vanishing_jet_is_ideal (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a q:
  is_commutative_ideal (@analytic_germ_jets_vanish_below R X NX hNX a q).
Proof.
constructor.
- move=>k hk;exact:analytic_germ_jet_zero.
- move=>alpha beta hA hB k hk.
  by rewrite analytic_germ_jet_add (hA k hk) (hB k hk) add0r.
- move=>alpha hA k hk.
  by rewrite analytic_germ_jet_negate (hA k hk) oppr0.
- move=>alpha beta hB.
  have hA:@analytic_germ_jets_vanish_below R X NX hNX a 0%N alpha.
    by move=>k;rewrite ltn0.
  have hh:=@analytic_product_vanishing_jets R X NX hNX a 0%N q alpha beta hA hB.
  by rewrite add0n in hh.
Qed.
