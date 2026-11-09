(** Federer (1969), 3.4.5, p. 319: the
    actual derivative-coordinate seminorm laws used in the
    original germ metric and continuity of ring operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermJetsSealed AnalyticGermGrowthUP AnalyticGermJetArithmetic AnalyticGermJetDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_jet_norm_nonnegative]: each
    actual derivative norm is nonnegative, 3.4.5, p. 319. *)
Lemma analytic_germ_jet_norm_nonnegative (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a):
  0<=@analytic_germ_jet_norm R X NX hNX a m alpha.
Proof.
exact:(real_seminorm_nonnegative
  (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
    (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))).1 _).
Qed.

(** Source for [analytic_germ_jet_norm_add]: the actual
    derivative norm satisfies the sum inequality on original
    germs, supporting 3.4.5, p. 319. *)
Lemma analytic_germ_jet_norm_add (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha beta:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  @analytic_germ_jet_norm R X NX hNX a m (alpha+beta)<=
    @analytic_germ_jet_norm R X NX hNX a m alpha+@analytic_germ_jet_norm R X NX hNX a m beta.
Proof.
rewrite /analytic_germ_jet_norm analytic_germ_jet_add.
exact:(real_seminorm_triangle
  (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
    (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))).1 _ _).
Qed.
