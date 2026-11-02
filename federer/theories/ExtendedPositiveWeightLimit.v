(** Federer (1969), proof of 2.4.6, p. 84: fixed positive real weights
    commute with increasing limits of measures. We prove the required
    order-interval statement directly, including infinite limits. Source
    editions: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_weight_increases]: supporting
    scalar limit passage for t*y_i*mu(B_i,n) in Federer
    2.4.6, p. 84; t and y_i are positive reals. *)
Lemma extended_positive_weight_increases (R : realType) (c : R)
    (u : nat -> \bar R) a :
  (0 < c)%R -> extended_increases_to u a ->
  extended_increases_to (fun n => c%:E * u n) (c%:E * a).
Proof.
move=> hc [hm [hl hu]]; split.
- move=> n m hnm; apply: lee_wpmul2l; first by rewrite lee_fin ltW.
  exact: hm n m hnm.
- split.
  + move=> b hb.
    have hb' : c^-1%:E * b < a by rewrite lte_pdivrMl.
    have [N hN] := hl _ hb'; exists N=> n hn.
    rewrite -lte_pdivrMl //; exact: hN hn.
  + move=> b hb.
    have hb' : a < c^-1%:E * b by rewrite lte_pdivlMl.
    have [N hN] := hu _ hb'; exists N=> n hn.
    rewrite -lte_pdivlMl //; exact: hN hn.
Qed.
