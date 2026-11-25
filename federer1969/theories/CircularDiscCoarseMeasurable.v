(** Federer (1969), 3.3.19, p. 304: original
    coarse level discs are measurable for every finer
    original hit measure. Actual ancestor containment and
    original separation discharge the whole-cell split. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscLevelPieces CircularDiscAncestors CircularDiscHitMeasureUP
  FiniteCellHitMeasureUP FiniteCellHitMeasurable MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Measurability.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_coarse_cell_split]: every
    original finer disc lies wholly in an original
    coarse disc or misses it, supporting the cyclic
    mass decomposition in 3.3.19, p. 304. *)
Lemma circular_disc_coarse_cell_split j k (a w:E):
  (j<=k)%N ->a \in H j ->w \in H k ->
  metric_closed_ball w (rho k) `<=` metric_closed_ball a (rho j) \/
    metric_closed_ball w (rho k) `&` metric_closed_ball a (rho j) = set0.
Proof.
move=>hjk ha hw.
have [z [hz hInside]]:=@circular_disc_ancestor_exists R H hH j k hjk w hw.
case:(eqVneq z a)=>[hEqual|hDifferent].
- left;by rewrite -hEqual.
- right;apply/seteqP;split=>[x [hxW hxA]|x []].
  have hxZ:=hInside x hxW.
  have hDisjoint:=@circular_disc_level_disjoint R H hH j z a hz ha hDifferent.
  have hFalse:(metric_closed_ball z (rho j) `&` metric_closed_ball a (rho j)) x by split.
  by rewrite hDisjoint in hFalse.
Qed.

(** Source for [circular_disc_coarse_disc_measurable]: the
    actual original coarse disc is Caratheodory measurable
    for every finer original psi, justifying the
    finite sums in 3.3.19, p. 304. No
    general Borel regularity of psi_n is asserted. *)
Theorem circular_disc_coarse_disc_measurable j k (a:E):
  (j<=k)%N ->a \in H j ->measure_measurable (psi k) (metric_closed_ball a (rho j)).
Proof.
move=>hjk ha;apply:(@finite_cell_hit_whole_cell_measurable R E E (H k)
  (fun z=>metric_closed_ball z (rho k)) (rho k) (psi k) (metric_closed_ball a (rho j)) (hPsi k)).
move=>w hw;exact:(@circular_disc_coarse_cell_split j k a w hjk ha hw).
Qed.
End Measurability.
