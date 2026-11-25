(** Federer (1969), 3.2.41, printed p. 277, first proof paragraph:
    the actual sum of two coordinate boxes is the box whose endpoints
    are the original endpoint sums. Every pair witness is local, and
    the opaque vector sum is used only through its independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  VectorSetSum EuclideanOpenCoordinateBoxUP ScalarOpenIntervalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_coordinate_box_sum]: supporting exact first
    product display in the proof of Federer 3.2.41, p. 277.
    The sum retains the original boxes and every original point,
    with no independent decomposition or measurability premise. *)
Theorem open_coordinate_box_sum (R : realType) n (a b c d : R_n R n)
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->
  is_euclidean_open_coordinate_box (a+c) (b+d) (vector_set_sum A B).
Proof.
move=> hA hB; split.
- move=> i; rewrite !ffunE; exact: ltrD (hA.1 i) (hB.1 i).
- move=> z; split.
  + move=> /vector_set_sum_membership [x [y [hx [hy ->]]]] i.
    have /andP[hax hxb] := (hA.2 x).1 hx i.
    have /andP[hcy hyd] := (hB.2 y).1 hy i.
    rewrite !ffunE; apply/andP; split; lra.
  + move=> hz.
    have hWitness i : exists p : R*R,
        [/\ a i<p.1<b i, c i<p.2<d i & z i=p.1+p.2].
      have hi := hz i; rewrite !ffunE in hi.
      have [x [y [hx [hy he]]]] :=
        (@scalar_open_interval_sum R (a i) (b i) (c i) (d i) (z i) (hA.1 i) (hB.1 i)).1 hi.
      exists (x,y); by split.
    pose p i := projT1 (cid (hWitness i)).
    pose x : R_n R n := [ffun i => (p i).1].
    pose y : R_n R n := [ffun i => (p i).2].
    apply/vector_set_sum_membership; exists x,y; split.
    * apply: (hA.2 x).2=> i; rewrite /x ffunE.
      have [hi _ _] := projT2 (cid (hWitness i)); exact hi.
    * split.
      -- apply: (hB.2 y).2=> i; rewrite /y ffunE.
         have [_ hi _] := projT2 (cid (hWitness i)); exact hi.
      -- apply/ffunP=> i; rewrite !ffunE.
         have [_ _ hi] := projT2 (cid (hWitness i)); exact hi.
Qed.
