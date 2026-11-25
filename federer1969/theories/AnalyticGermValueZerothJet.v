(** Federer (1969), 3.4.8(6), p. 329:
    zero centre value is the actual zero zeroth
    derivative in the positive-order choice. The
    established representative theorem descends to all germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws
  AnalyticGermValueUP AnalyticGermValueSealed AnalyticGermZerothVanishing
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_germ_value_zeroth_jet]: the
    actual value and derivative definitions give
    equivalent zero conditions, supporting the positive
    order in 3.4.8(6), p. 329. *)
Lemma analytic_germ_value_zeroth_jet (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (alpha:@analytic_germ_ring R X NX hNX a):
  @AnalyticGermValue.map R X NX hNX a alpha = 0 <->
  @AnalyticGermJets.value R X NX hNX a 0%N alpha = 0.
Proof.
have [f <-]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite (@AnalyticGermValue.laws R X NX hNX a f).
exact:(@analytic_germ_zeroth_vanishing R X NX hNX a f).
Qed.
