(** Federer (1969), 3.1.24, pp. 237–239:
    nonnegativity of the analytic bound is a consequence
    of the defining first-order estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_operator_witness_nonnegative]: supporting
    the nonnegative parameters in the composition estimate of
    Federer 3.1.24, p. 239. An existing first
    differential has nonnegative operator norm, so its bound
    by c implies 0<=c. No new hypothesis is added
    to the printed analytic condition. *)
Lemma norm_analytic_operator_witness_nonnegative (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (f:X->Y) a c :
  U a -> norm_class_all_orders hNX hNY U f ->
  (forall m,(1<=m)%N -> forall x,U x ->
    forall z:@ContinuousMultilinear.space R m X Y NX NY hNX hNY,
      has_norm_higher_differential NX
        (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
        (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) U f m x z ->
      @ContinuousMultilinear.norm R m X Y NX NY hNX hNY z<=c^+m*(m`!)%:R) -> 0<=c.
Proof.
move=>ha hf hb.
have [_ [D [hD hc]]]:=hf 1%N.
have hh:=hb 1%N (leqnn 1%N) a ha (D a) (hD a ha).
rewrite expr1 /= ?mulr1 in hh.
have hn:=multilinear_operator_nonnegative
  (continuous_multilinear_norm_laws (@ContinuousMultilinear.laws R 1%N X Y NX NY hNX hNY) (D a)).
exact (le_trans hn hh).
Qed.
