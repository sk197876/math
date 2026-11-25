(** Federer (1969), 2.3.3, p. 76: the greedy selected-weight series equals
    its nonnegative extended-real target. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP GreedyScalarBounds GreedyScalarOmissions
  WeightedCharacteristicExpansionUP NonnegativeSum ExtendedRealReciprocalBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_scalar_series_exact]: direct pointwise numerical
    argument proving Federer 2.3.3, p. 76 The target may be positive
    infinity; no subtraction of infinite quantities is used. *)
Theorem greedy_scalar_series_exact (R : realType) (r : nat -> R) (t : \bar R) s :
  is_positive_vanishing_divergent_sequence r -> 0 <= t ->
  is_greedy_scalar_expansion r t s ->
  nonnegative_sum setT (fun n => (greedy_scalar_term r t s n)%:E) = t.
Proof.
move=> hw ht hs.
have hr n : (0 <= r n)%R := ltW (expansion_weights_positive hw n).
pose S := nonnegative_sum setT (fun n => (greedy_scalar_term r t s n)%:E).
have hS0 : 0 <= S := nonnegative_sum_nonnegative _ _.
have hSt : S <= t := @greedy_scalar_series_upper R r t s hr ht hs.
apply/eqP; rewrite eq_le hSt /=.
change (t <= S).
case hS : S=> [v| |] in hS0 hSt *; [|exact (leey t)|by []].
apply: extended_real_reciprocal_upper_bound=> k.
pose eps := (((k.+1)%:R : R)^-1)%R.
have hep : (0 < eps)%R by rewrite /eps invr_gt0 ltr0n.
have hepE : (0 : \bar R) < eps%:E by rewrite lte_fin.
have [N hN] := (expansion_weights_vanish hw).2 eps%:E hepE.
have hfin : S < +oo by rewrite hS ltry.
have [n [hn hno]] := @greedy_scalar_arbitrarily_late_omissions R r t s hr
  (expansion_weights_diverge hw) hfin N.
have hpn : (s n)%:E <= v%:E.
  rewrite -hS -(@greedy_scalar_prefix_sum R r t s hr hs n).
  apply: nonnegative_sum_subset=> i _; exact Logic.I.
have hlt : t < (s n + r n)%R%:E by rewrite ltNge.
have hb : (s n + r n)%R%:E <= (v + eps)%R%:E.
  rewrite !EFinD; exact: leeD hpn (ltW (hN n hn)).
exact: ltW (lt_le_trans hlt hb).
Qed.
