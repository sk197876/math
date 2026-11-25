(** Federer (1969), 2.1.1, p. 51, the extended real line with its usual
    order topology, supporting the rational-ray criterion of 2.3.2(2), p.
    73. The general order-topology background is reused; no external
    measurable-real-function theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_line]: supporting explicit order-
    topology carrier from Federer 2.1.1, p. 51, for
    the extended-real measurable functions in 2.3.2, pp. 73–75. *)
Definition extended_real_line (R : realType) : topologicalType :=
  [the topologicalType of order_topology (\bar R)].

(** Source for [extended_rationals_order_dense]: supporting
    density fact for the rational-ray criterion of Federer
    2.3.2(2), p. 73. A finite rational lies strictly
    between any two distinct ordered extended reals, including
    intervals with one or both infinite endpoints. *)
Lemma extended_rationals_order_dense (R : realType) :
  is_order_dense_family (fun q : rat => (ratr q : R)%:E).
Proof.
move=> [a| |] [b| |] //= hab.
- have habR : (a < b)%R := hab.
  have [q hq] := rat_in_itvoo habR.
  have /andP[hq1 hq2] : ((a < ratr q < b)%R) := hq.
  exists q; split; rewrite lte_fin; [exact: hq1|exact: hq2].
- have hh : (a < a + 1)%R by rewrite ltrDl ltr01.
  have [q hq] := rat_in_itvoo hh.
  move: hq; rewrite interval.in_itv /= => /andP[hq1 hq2].
  exists q; split; [rewrite lte_fin; exact: hq1|exact: ltry].
- have hh : (b - 1 < b)%R by rewrite ltrBlDr ltrDl ltr01.
  have [q hq] := rat_in_itvoo hh.
  move: hq; rewrite interval.in_itv /= => /andP[hq1 hq2].
  exists q; split; [exact: ltNyr|rewrite lte_fin; exact: hq2].
- exists 0%Q; split; [exact: ltNyr|exact: ltry].
Qed.
