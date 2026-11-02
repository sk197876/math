(** Federer (1969), proof of 2.4.3(6), p. 82: supporting choice of two
    strict real upper bounds whose sum stays below a given strict bound. We
    prove the needed order statement from rational density, including
    negative-infinite summands. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_sum_strict_real_upper_bounds]: the
    approximation step in Federer 2.4.3(6), p. 82.
    Both summands must be below positive infinity, exactly as
    in the application to finite-upper-integral approximants. *)
Lemma extended_sum_strict_real_upper_bounds (R : realType) (a b z : \bar R) :
  a < +oo -> b < +oo -> a+b < z ->
  exists r s : R, a < r%:E /\ b < s%:E /\ (r+s)%:E < z.
Proof.
move=> ha hb hab.
have [q [hq hqz]] := @extended_rationals_order_dense R (a+b) z hab.
clear hab; pose t := (ratr q : R).
have hat : a < t%:E-b.
  case: a ha hq=> [a| |] ha hq //.
  - by rewrite lte_suber_addr //.
  - case: b hb hq=> [b| |] hb hq //; by rewrite ?ltNyr.
have [qr [har hrt]] := @extended_rationals_order_dense R a (t%:E-b) hat.
pose r := (ratr qr : R).
have hbt : b < t%:E-r%:E.
  rewrite lteBrDr // addeC; by move: hrt; rewrite lte_suber_addr.
have [qs [hbs hst]] := @extended_rationals_order_dense R b (t%:E-r%:E) hbt.
exists r, (ratr qs : R); split=> //; split=> //.
apply: lt_trans _ hqz; rewrite EFinD addeC.
by move: hst; rewrite lteBrDr.
Qed.
