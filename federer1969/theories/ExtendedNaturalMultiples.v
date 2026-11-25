(** Federer (1969), proof of 2.4.4(2), p. 83: a lower integral dominating n
    times a fixed positive measure for every natural n must be positive
    infinity. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_natural_multiples_force_infinity]:
    supporting Archimedean implication in Federer 2.4.4(2),
    p. 83; the fixed positive measure may itself be infinite. *)
Lemma positive_natural_multiples_force_infinity (R : realType) (m L : \bar R) :
  0 < m -> (forall n : nat, n%:R%:E * m <= L) -> L=+oo.
Proof.
move=> hm hL; case: m hm hL=> [p| |] hm hL; last by [].
- case: L hL=> [l| |] hL.
  + pose n := Num.bound `|l/p|%R.
    have hn : (l/p < n%:R)%R := le_lt_trans (ler_norm _) (archi_boundP (normr_ge0 _)).
    have hnp : (l < n%:R * p)%R by rewrite -ltr_pdivrMr.
    have h := hL n; rewrite -EFinM lee_fin in h.
    by move: hnp; rewrite ltNge h.
  + by [].
  + have h := hL 0%N; by rewrite mul0e leNgt ltNyr in h.
- have h := hL 1%N; rewrite mul1e leye_eq in h; exact/eqP.
Qed.
