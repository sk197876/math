(** Federer (1969), 2.10.29, p. 193: the real power cost of an interval
    square of side r is b*2^m*(r^m)^2 in degree 2m. This supporting scalar
    identity leaves the positive normalisation b explicit. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealPower RealPowerContinuity RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [power_cantor_square_cost]: direct scalar
    simplification of the equal-width square
    covers in 2.10.29, p. 193. The
    side length may be zero; m is positive. *)
Lemma power_cantor_square_cost (R : realType) (b m r : R) :
  0<m -> 0<=r ->
  b*real_power (Num.sqrt 2*r) (2 * m)=b*real_power 2 m*(real_power r m)^+2.
Proof.
move=> hm hr.
have htwo : (0<2 :> R) by rewrite ltr0n.
have hs : (0<=Num.sqrt (2 : R)) := sqrtr_ge0 _.
have hroot : real_power (Num.sqrt (2 : R)) (2 * m)=real_power 2 m.
  have hh := @real_power_positive_iterate R (Num.sqrt 2) 2 m hs htwo hm.
  by rewrite real_power_two // sqr_sqrtr ?ltW // in hh.
have hdouble : real_power r (2 * m)=(real_power r m)^+2.
  have he : 2 * m=m+m by ring.
  have [->|hrne] := eqVneq r 0.
  - by rewrite !real_power_zero_base ?gt_eqF ?mulr_gt0 // expr2 mulr0.
  have hrpos : 0<r by rewrite lt_neqAle eq_sym hrne hr.
  by rewrite he real_power_add_exponents_positive // expr2.
by rewrite real_power_product // hroot hdouble mulrA.
Qed.
