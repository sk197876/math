(** Supporting Federer (1969), 2.10.46, p. 204: the projected-volume cost of
    a set bounds the cost of a parameter set whose horizontal sections have
    uniformly positive first-factor volume. Apply each block projection
    (x,y) maps to (x,q(y)), the section-cover lower bound, and the
    projected-volume supremum. This is the geometric step needed to extend
    the opposite Gross inequality using 2.10.8, p. 175. No measurability of
    the input sets is imposed here. Source context and projection
    conventions: EuclideanBlockProjection.v; the covering argument:
    ProductSectionOuterBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockProjection EuclideanSectionOuterBound
  EuclideanLebesgueDimensions MeasureUP MeasureBasic ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_horizontal_sections_gauge_lower_bound]:
    supporting Gross lower-bound comparison in 2.10.46,
    p. 204. Each second-factor projection is extended by
    the identity on the first factor, as in 1.7.4,
    pp. 30–31. Uniformly positive section volume supplies
    the scalar factor before taking the projection supremum. *)
Theorem projected_horizontal_sections_gauge_lower_bound (R : realType) m n k
    (H : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (B : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (0<c)%R -> (forall y, B y -> c%:E<=euclidean_lebesgue_measure m
    [set x | H (@euclidean_block_join R m n (x,y))]) ->
  c%:E*@projected_volume_gauge R n k B<=@projected_volume_gauge R (m+n) (m+k) H.
Proof.
move=> hc hsec; rewrite -lee_pdivlMl //; apply: projected_volume_gauge_least_bound=> q hq.
rewrite lee_pdivlMl //.
pose f := GRing.Linear.clone _ _ _ _ (@euclidean_block_projection R m n k q) _.
have hf := @euclidean_block_projection_orthogonal R m n k q hq.
apply: le_trans _ (@projected_volume_gauge_projection_bound R (m+n) (m+k) H f hf).
apply: (@euclidean_horizontal_sections_outer_lower_bound R m k (f @` H) (q @` B) c hc).
move=> z [y hy <-]; apply: le_trans (hsec y hy) _.
apply: (measure_mono (euclidean_lebesgue_is_measure R m))=> x hx.
exists (@euclidean_block_join R m n (x,y))=> //.
exact: euclidean_block_projection_pair.
Qed.
