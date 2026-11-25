(** Federer (1969), 2.10.28(3), p. 192: supporting nested level unions and
    persistence of a positive-cost member in the limit. Only positive-cost
    descendants need this point: a zero-cost singleton may have an empty
    child family under the printed special-family laws. The proof below
    retains those allowed degenerate branches and uses compactness for the
    positive-cost case. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalTreeLevels SpecialIntervalDescendants
  CompactDecreasingNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_level_union_step]: direct
    inclusion of each next level union in
    its preceding level in 2.10.28(3),
    p. 192, by child-parent containment. *)
Lemma special_interval_level_union_step (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j :
  (\bigcup_(S in [set` H j.+1]) val S) `<=` \bigcup_(S in [set` H j]) val S.
Proof.
move=> x [S hS hxS]; have [T [hT hsub]] := @special_tree_refinement R h H ht j S hS.
exists T; first exact hT; exact: hsub x hxS.
Qed.

(** Source for [special_interval_level_union_after]: supporting
    iterated level containment in 2.10.28(3),
    p. 192, including zero iterations. *)
Lemma special_interval_level_union_after (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j n :
  (\bigcup_(S in [set` H (j+n)%N]) val S) `<=` \bigcup_(S in [set` H j]) val S.
Proof.
elim: n=> [|n ih]; first by rewrite addn0.
rewrite addnS=> x hx.
exact (ih x (@special_interval_level_union_step R h H ht (j+n)%N x hx)).
Qed.

(** Source for [special_interval_level_union_antitone]: supporting
    decreasing compact sequence for the limit
    in 2.10.28(3), p. 192. *)
Lemma special_interval_level_union_antitone (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) m n :
  (m<=n)%N ->
  (\bigcup_(S in [set` H n]) val S) `<=` \bigcup_(S in [set` H m]) val S.
Proof.
move=> hmn; have heq : n=(m+(n-m))%N by rewrite addnC subnK.
rewrite heq; exact (@special_interval_level_union_after R h H ht m (n-m)%N).
Qed.

(** Source for [positive_interval_member_meets_limit]: supporting point
    selection in the lower-bound proof of 2.10.28(3), p. 192 Positive cost
    forces nonempty descendants at all later levels; nested compactness
    gives a point of the limit in this member. No assertion of persistence
    is needed for zero-cost dead branches. *)
Theorem positive_interval_member_meets_limit (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) (A : set (real_line_metric R))
    (hA : is_special_interval_tree_limit H A) j (S : compact_real_intervals R) :
  S \in H j -> 0<concave_interval_cost h (val S) -> A `&` val S !=set0.
Proof.
move=> hS hpos.
pose B n := \bigcup_(U in [set` H n]) val U.
pose C n := val S `&` B n.
have hBclosed n : closed (B n).
  apply: closed_bigcup; first exact: finite_fset.
  move=> U _; exact: compact_real_interval_closed (set_valP U).
have hCclosed n : closed (C n) := closedI (compact_real_interval_closed (set_valP S)) (hBclosed n).
have hC0 : compact (C 0%N) := compact_closedI (compact_real_interval_compact (set_valP S)) (hBclosed 0%N).
have hCdec n m (hnm : (n<=m)%N) : C m `<=` C n.
  move=> x [hxS hxB]; split=> //.
  exact: (@special_interval_level_union_antitone R h H ht n m hnm x hxB).
have hCne n : C n !=set0.
  pose G := special_interval_restriction (H (j+n)%N) (val S).
  have hG := @special_interval_descendants_special R h hg H ht j S hS n.
  have hcost := @special_interval_cost_sum R h S G hG.
  have hneG : exists U, U \in G.
    apply: contrapT=> hnone.
    have he : G=fset0.
      apply/fsetP=> U; rewrite in_fset0; apply/negP=> hU; apply: hnone; by exists U.
    rewrite he big_seq_fset0 in hcost; by rewrite hcost ltxx in hpos.
  have [U hUG] := hneG.
  have [hU hUS] := (special_interval_restriction_membership _ _ _).1 hUG.
  have [x hxU] := compact_real_interval_nonempty (set_valP U).
  have hxlater : B (j+n)%N x by exists U; [exact hU | exact hxU].
  have hsub : B (j+n)%N `<=` B n.
    rewrite /B addnC; exact (@special_interval_level_union_after R h H ht n j).
  exists x; split; [exact: hUS x hxU | exact: hsub x hxlater].
apply: contrapT=> hnone.
have hsmall : (\bigcap_n C n) `<=` set0.
  move=> x hx; apply: hnone.
  have hxS : val S x := (hx 0%N Logic.I).1.
  have hxA : A x.
    apply/(hA x)=> n; have [U hU hxU] := (hx n Logic.I).2.
    exists U; by split.
  exists x; by split.
have [N hN] := @compact_decreasing_eventually_in_open (real_line_metric R) C set0
  hC0 hCclosed hCdec open0 hsmall.
have [x hx] := hCne N; exact: hN N (leqnn N) x hx.
Qed.
