(** Federer (1969), 2.4.17, p. 90: continuity in the extended real line,
    whose topology is specified in 2.1.1, p. 51. This general-topology
    adapter identifies the project's order-limit predicate with convergence
    in its public extended-real order topology. No external integration or
    norm-continuity result is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CountableOrderIntervals ExtendedRealOrderTopology ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit_topology_iff]: supporting equivalence
    of order intervals and topological sequence convergence for Federer
    2.4.17, p. 90 *)
Lemma extended_order_limit_topology_iff (R : realType) (u : nat -> \bar R) l :
  ((fun n => (u n : extended_real_line R)) @ \oo --> (l : extended_real_line R)) <->
  extended_order_limit u l.
Proof.
split.
- move=> h; split=> a ha.
  + have ho := @order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] a.
    have hn : nbhs (l : extended_real_line R) [set y | a < y].
      rewrite openE in ho; exact: ho l ha.
    have [k _ hk] := h _ hn; exists k=> n hkn; exact: hk n hkn.
  + have ho := @order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] a.
    have hn : nbhs (l : extended_real_line R) [set y | y < a].
      rewrite openE in ho; exact: ho l ha.
    have [k _ hk] := h _ hn; exists k=> n hkn; exact: hk n hkn.
- move=> [hlo hup] B hB.
  rewrite itv_nbhsE in hB; have [it [hoi hli] hiB] := hB.
  case: it hoi hli hiB=> [[[] a|[]]] [[] b|[]] //= _ hli hiB; rewrite interval.in_itv /= ?andbT in hli.
  + have /andP[hal hlb] := hli; have [k hk] := hlo a hal; have [j hj] := hup b hlb.
    exists (maxn k j); first exact Logic.I.
    move=> n hn; apply: hiB; rewrite /= interval.in_itv /=; apply/andP; split.
    * exact: hk n (leq_trans (leq_maxl k j) hn).
    * exact: hj n (leq_trans (leq_maxr k j) hn).
  + have [k hk] := hlo a hli; exists k; first exact Logic.I.
    move=> n hn; apply: hiB.
    by rewrite /= interval.in_itv /= andbT; exact: hk n hn.
  + have [k hk] := hup b hli; exists k; first exact Logic.I.
    move=> n hn; apply: hiB.
    by rewrite /= interval.in_itv /=; exact: hk n hn.
  + exists 0%N; first exact Logic.I.
    move=> n hn; apply: hiB; by rewrite /= interval.in_itv.
Qed.
