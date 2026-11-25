(** Federer (1969), 2.4.16, pp. 89–90: supporting power comparison for
    bounded integrable test weights. Source context:
    PositiveIntegrableWeightUP.v. A weight bounded by one is a unit-ball
    candidate for every finite exponent at least one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_unit_interval_bound]: supporting
    inequality w^q<=w for q>=1 and 0<=w<=1, used in the test
    construction for Federer 2.4.16, p. 90. *)
Lemma real_power_unit_interval_bound (R : realType) (q w : R) :
  1 <= q -> 0 <= w -> w <= 1 -> real_power w q <= w.
Proof.
move=> hq hw hw1; have [->|hq1] := eqVneq q 1.
- by rewrite real_power_one_exponent.
have hqgt : 1 < q by rewrite lt_neqAle eq_sym hq1 hq.
have hd : 0 < q-1 by rewrite subr_gt0.
have hh := @real_power_monotone R w 1 (q-1) hw hw1 hd.
rewrite real_power_one_base in hh.
have he : q=(q-1)+1 by rewrite subrK.
rewrite he real_power_positive_successor //.
have hb := ler_wpM2r hw hh; by rewrite mul1r in hb.
Qed.
