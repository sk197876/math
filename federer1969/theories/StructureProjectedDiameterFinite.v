(** Federer (1969), 3.3.8, p. 295: every original
    small-diameter source has finite projected Lebesgue outer mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  MetricClosedBalls EuclideanClosedBallVolume EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projected_diameter_mass_finite]: the
    finite L^m[p(E)] assertion at the end of Federer 3.3.8,
    p. 295. A local original point centres a ball containing
    the entire original projected image by contraction. Empty
    sources, degree zero and nonmeasurable images are retained. *)
Theorem structure_projected_diameter_mass_finite (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (a:R):
  0<=a ->(forall x y,E x ->E y ->mdist x y<=a) ->
  (euclidean_lebesgue_measure m (euclidean_projection_linear p @` E)< +oo)%E.
Proof.
move=>ha hDiameter.
case:(pselect (exists x,E x))=>[[x hx]|hEmpty].
- have hSubset:(euclidean_projection_linear p @` E) `<=`
      metric_closed_ball (euclidean_projection_linear p x:
        inner_metric_space (@euclidean_inner_productP R m)) a.
    move=>z [y hy <-]; rewrite /metric_closed_ball /=.
    exact:le_trans (euclidean_projection_nonexpanding p x y) (hDiameter x y hx hy).
  have hBound:=@measure_mono R _ (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) _ _ hSubset.
  rewrite (euclidean_closed_ball_normalized_volume _ ha) in hBound.
  exact:le_lt_trans hBound (ltry _).
- have hImage:(euclidean_projection_linear p @` E)=set0.
    apply/seteqP; split; last by [].
    move=>z [x hx _]; exfalso; apply:hEmpty; by exists x.
  rewrite hImage (measure_empty (euclidean_lebesgue_is_measure R m)); exact:lt0y.
Qed.
