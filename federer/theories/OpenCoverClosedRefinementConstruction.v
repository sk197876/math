(** Federer (1969), 2.2.16, pp. 71–72: private construction of C_n(V) by
    well-ordering the open family, removing all preceding members and
    requiring distance at least 1/n from the complement of V. The universal
    interior-core predicate handles empty complements. General set-theoretic
    well ordering is the same background used in 2.1.6, with order laws
    documented from Kelley, Appendix, p. 263. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology wochoice.
From Federer Require Import WellOrderLaws MetricInteriorCores OpenCoverClosedRefinementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_closed_open_refinement_exists]: direct
    existence construction of C_n(V) in Federer 2.2.16,
    pp. 71–72. Well ordering gives a first open
    set containing each point of the union. Every subfamily
    union at a fixed level will be closed by separation. *)
Theorem separated_closed_open_refinement_exists (R : realType) (X : metricType R)
    (J : choiceType) (D : set J) (U : J -> set X) :
  (forall j, D j -> open (U j)) -> exists C, is_separated_closed_open_refinement D U C.
Proof.
move=> ho; have [ord hw] := well_ordering_principle J.
pose P j := \bigcup_(i in [set i | D i /\ ord i j /\ i <> j]) U i.
pose r n : R := ((n.+1)%:R)^-1.
pose C n j := metric_interior_core (U j) (r n) `\` P j.
have hr n : 0 < r n by rewrite /r invr_gt0 ltr0n.
have hP j : open (P j).
  apply: bigcup_open=> i [hi _]; exact: ho i hi.
have hinside n j : C n j `<=` U j.
  move=> x [hx _]; exact: (@metric_interior_core_inside R X (U j) (r n) (hr n) x hx).
exists C; constructor.
- move=> n j hj; apply: closedI; first exact: metric_interior_core_closed.
  exact: open_closedC (hP j).
- move=> n j hj; exact: hinside n j.
- apply/seteqP; split.
  + move=> x hx.
    have hex : exists j, D j /\ U j x by have [j hj hxj] := hx; exists j.
    have [j [[hj hxj] hmin]] := @well_order_set_minimum J ord
      [set j | D j /\ U j x] hw hex.
    have [n hn] := open_set_covered_by_reciprocal_cores (ho j hj) hxj.
    exists n; first exact Logic.I; exists j=> //; split; first exact hn.
    move=> [i [hi [hij hne]] hxi]; apply: hne.
    have hji := hmin i (conj hi hxi).
    apply: (@well_order_antisymmetric_law J ord hw i j); by apply/andP; split.
  + move=> x [n _ [j hj hx]]; exists j=> //; exact: hinside n j x hx.
- move=> n j k hj hk hne x y [hx hxp] [hy hyp].
  have /orP[hjk|hkj] := @well_order_total_law J ord hw j k.
  + apply: hx=> hyj; apply: hyp; exists j=> //; by split=> //; split.
  + rewrite metric_sym; apply: hy=> hxk; apply: hxp; exists k=> //.
    split=> //; split=> // hkj0; apply: hne; exact: esym hkj0.
Qed.
