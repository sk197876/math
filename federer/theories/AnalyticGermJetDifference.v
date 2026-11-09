(** Federer (1969), 3.4.5, p. 319: subtraction
    of original germs commutes with every actual derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  ContinuousMultilinearSealed AnalyticGermJetsSealed AnalyticGermJetArithmetic AnalyticGermJetZeroNegate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_jet_difference]: actual
    derivative subtraction for the metric and continuous
    operations in 3.4.5, p. 319. *)
Lemma analytic_germ_jet_difference (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha beta:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  @AnalyticGermJets.value R X NX hNX a m (alpha-beta)=
    @AnalyticGermJets.value R X NX hNX a m alpha-@AnalyticGermJets.value R X NX hNX a m beta.
Proof.
change (@AnalyticGermJets.value R X NX hNX a m
  (@AnalyticGerms.add R X NX hNX a alpha (@AnalyticGerms.opp R X NX hNX a beta))=
  @AnalyticGermJets.value R X NX hNX a m alpha-@AnalyticGermJets.value R X NX hNX a m beta).
by rewrite analytic_germ_jet_add analytic_germ_jet_negate.
Qed.
