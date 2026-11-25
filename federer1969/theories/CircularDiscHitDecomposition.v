(** Federer (1969), 3.3.19, p. 304: the
    original finer psi decomposes over the original
    coarser discs for every original test set. Prove
    all measurable splitting inputs from actual whole-disc
    containment, without imposing additivity on arbitrary sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscLevelPieces CircularDiscAncestors CircularDiscCoarseMeasurable
  CircularDiscHitMeasureUP CircularDiscHitMeasureLaws FiniteCellHitMeasureUP FiniteCellHitRestriction
  MeasureUP MeasureRestriction MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Decomposition.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_fine_cells_coarse_union]:
    every original fine cell lies in the actual
    original coarse level union, supporting the restricted
    hit-count sum in 3.3.19, p. 304. *)
Lemma circular_disc_fine_cells_coarse_union j k:(j<=k)%N ->forall w:E,w \in H k ->
  metric_closed_ball w (rho k) `<=` circular_disc_level_union H j.
Proof.
move=>hjk w hw.
have [z [hz hInside]]:=@circular_disc_ancestor_exists R H hH j k hjk w hw.
move=>x hx;exists z;split=>//;exact:hInside x hx.
Qed.

(** Source for [circular_disc_hit_coarse_decomposition]:
    literal finite equality psi_k(T)=sum_{B in G_j}
    psi_k(T intersect B) for every original finer
    level k>=j, as used in the cyclic sum
    of 3.3.19, p. 304. The original T
    may be nonmeasurable. Restrict the outer measure
    to T, then use proved measurable coarse discs. *)
Theorem circular_disc_hit_coarse_decomposition j k (T:set E):(j<=k)%N ->
  psi k T=\sum_(z<-H j) psi k (T `&` metric_closed_ball z (rho j)).
Proof.
move=>hjk.
have hRestrict:=@finite_cell_hit_support_restriction R E E (H k)
  (fun z=>metric_closed_ball z (rho k)) (rho k) (psi k) (circular_disc_level_union H j) T
  (hPsi k) (@circular_disc_fine_cells_coarse_union j k hjk).
have hm:=@circular_disc_hit_is_measure R H psi hPsi k.
have hRestricted:=@measure_restrict_is_measure R E (psi k) hm T.
have hMeas z:z \in H j ->measure_measurable (measure_restrict (psi k) T) (metric_closed_ball z (rho j)).
  move=>hz;apply:measure_restrict_measurable.
  exact:(@circular_disc_coarse_disc_measurable R H hH psi hPsi j k z hjk hz).
have hDisjoint z w:z \in H j ->w \in H j ->z!=w ->
    forall x,metric_closed_ball z (rho j) x ->metric_closed_ball w (rho j) x ->False.
  move=>hz hw hZW x hx hy.
  have hEmpty:=@circular_disc_level_disjoint R H hH j z w hz hw hZW.
  have hFalse:(metric_closed_ball z (rho j) `&` metric_closed_ball w (rho j)) x by split.
  by rewrite hEmpty in hFalse.
have hSum:=@measure_finite_disjoint_additivity R E E (measure_restrict (psi k) T) hRestricted
  (fun z=>metric_closed_ball z (rho j)) (H j) hMeas hDisjoint.
have hUnion:(\bigcup_(z in [set` H j]) metric_closed_ball z (rho j))=circular_disc_level_union H j.
  apply/seteqP;split.
  - move=>x [z hz hx];by exists z;split.
  - move=>x [z [hz hx]];by exists z.
rewrite /measure_restrict hUnion -hRestrict in hSum.
exact hSum.
Qed.
End Decomposition.
