(** Federer (1969), 2.3.2(8)–(9), pp. 74–75: dist(A,B) is the infimum of all
    cross distances. The empty infimum is positive infinity, as in 2.1.1, p.
    51. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds MeasurableSeparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_set_cross_distances]: direct range of the
    metric on A times B in Federer 2.3.2(8), p. 74. *)
Definition metric_set_cross_distances (R : realType) (Y : metricType R) (A B : set Y) : set (\bar R) :=
  [set t | exists x, A x /\ exists y, B y /\ t = (mdist x y)%:E].

(** Source for [metric_set_distance_infimum]: direct dist(A,B)
    in Federer 2.3.2(8), p. 74, specified by the sealed
    extended-real infimum laws, including empty A or B. *)
Definition metric_set_distance_infimum (R : realType) (Y : metricType R) (A B : set Y) :=
  extended_real_inf (metric_set_cross_distances A B).

(** Source for [metric_positive_infimum_separation_iff]: supporting
    equivalence between the book's positive infimum and a positive
    uniform real lower bound in Federer 2.3.2(8)–(9),
    pp. 74–75. Empty sets satisfy both formulations. *)
Theorem metric_positive_infimum_separation_iff (R : realType) (Y : metricType R) (A B : set Y) :
  (0 < metric_set_distance_infimum A B) <-> metric_sets_positively_separated A B.
Proof.
split.
- move=> hp; have [delta [hd hbound]] : exists delta : R,
      (0 < delta)%R /\ delta%:E <= metric_set_distance_infimum A B.
    case he : (metric_set_distance_infimum A B)=> [d| |] in hp *.
    + exists d; split=> //; by move: hp; rewrite lte_fin.
    + exists 1%R; by split; [exact: ltr01|exact: leey].
    + by [].
  exists delta; split=> // x hx y hy.
  have hm := @extended_real_inf_lower R (metric_set_cross_distances A B) (mdist x y)%:E.
  have hmem : metric_set_cross_distances A B (mdist x y)%:E by exists x; split=> //; exists y.
  have h := le_trans hbound (hm hmem); by move: h; rewrite lee_fin.
- move=> [delta [hd hs]].
  have hl : delta%:E <= metric_set_distance_infimum A B.
    apply: extended_real_inf_greatest=> t [x [hx [y [hy ->]]]].
    rewrite lee_fin; exact: hs x hx y hy.
  apply: lt_le_trans _ hl; by rewrite lte_fin.
Qed.
