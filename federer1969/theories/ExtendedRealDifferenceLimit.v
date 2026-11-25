(** Federer (1969), 2.1.1(13), p. 53: passage to a defined difference of
    increasing nonnegative limits. This proof uses the order intervals
    directly. Source context: ExtendedRealOrderLimit.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_nonnegative_difference_limit]: Federer
    2.1.1(13), p. 53; supporting limit law for variations bounded
    by their nonnegative limits, with at least one limit finite.
    Both finite and infinite resulting limits are retained. *)
Lemma extended_nonnegative_difference_limit (R : realType)
    (p n : nat -> \bar R) P N :
  0 <= P -> 0 <= N -> (P < +oo) || (N < +oo) ->
  (forall k, p k <= P) -> (forall k, n k <= N) ->
  extended_order_limit p P -> extended_order_limit n N ->
  extended_order_limit (fun k => p k-n k) (P-N).
Proof.
move=> hP hN hd hp hn [hpl hpu] [hnl hnu]; split.
- move=> a ha; case he: N=> [r| |].
  + have hac : a+r%:E < P by move: ha; rewrite he lteBrDr.
    have [K hK] := hpl _ hac; exists K=> k hk.
    have hlow : a < p k-r%:E by rewrite lteBrDr //; exact: hK.
    apply: lt_le_trans hlow _; apply: leeB; first exact: lexx.
    by rewrite -he.
  + by move: ha; rewrite he addeNy ltNge leNye.
  + by move: hN; rewrite he.
- move=> b hb; case he: P=> [r| |].
  + have hbc : r%:E-b < N.
      move: hb; rewrite he lte_subel_addr //.
      by rewrite lte_subel_addr // addeC.
    have [K hK] := hnl _ hbc; exists K=> k hk.
    have hupp : r%:E-n k < b.
      rewrite lte_subel_addr // addeC -lte_subel_addr //; exact: hK.
    apply: le_lt_trans _ hupp; apply: leeB; last exact: lexx.
    by rewrite -he.
  + move: hd hb hN; rewrite he ltxx /=; case hne: N=> [r| |] // _.
    by rewrite addye // ltNge leey.
  + by move: hP; rewrite he.
Qed.
