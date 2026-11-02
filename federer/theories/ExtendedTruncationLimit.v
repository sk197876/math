(** Federer (1969), proof of 2.4.11, p. 86: the finite ceilings n increase
    without bound, so min{|f|,n} increases to |f|, including infinite
    values. The supporting scalar proof uses only order intervals and the
    Archimedean real-field background. Source context:
    PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_natural_upper_truncations_increase]:
    supporting scalar increasing convergence of the truncations
    in Federer 2.4.11, proof p. 86. *)
Lemma extended_natural_upper_truncations_increase (R : realType) (z : \bar R) :
  extended_increases_to (fun n => Order.min z (n.+1)%:R%:E) z.
Proof.
split.
- move=> n m hnm; apply: le_min2; first exact: lexx.
  by rewrite lee_fin ler_nat.
- split.
  + move=> a ha; have [q [haq hqz]] := @extended_rationals_order_dense R a z ha.
    pose N := Num.bound (`|ratr q : R|).
    have hqN : ((ratr q : R) < N%:R)%R.
      have hb : (`|ratr q : R| < N%:R)%R := archi_boundP (normr_ge0 (ratr q : R)).
      exact: le_lt_trans (ler_norm (ratr q : R)) hb.
    exists N=> n hn; apply: lt_trans haq _; rewrite lt_min hqz /= lte_fin.
    apply: lt_le_trans hqN _; rewrite ler_nat; exact: leq_trans hn (leqnSn n).
  + move=> b hb; exists 0%N=> n _; apply: le_lt_trans _ hb.
    by rewrite ge_min lexx orTb.
Qed.
