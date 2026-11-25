(** Federer (1969), 2.10.47, pp. 204–205: every positive compact set
    contains a compact subset of finite positive measure. This file
    discharges the temporary null-section hypothesis by induction on ambient
    dimension. A positive coordinate section uses the induction hypothesis;
    otherwise the proved compact pruning applies. The positive real exponent
    and positive normalising coefficient are explicit. Degree zero is
    handled by HausdorffFinitePositiveSubsetBase.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CompactHyperplaneReduction CompactNullSectionsSubset RealPowerSingletonBound
  MetricRealPowerMeasureUP MetricRealPowerMeasure MetricRealPowerMeasureLaws
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_real_power_compact_subset]: the
    positive-degree theorem 2.10.47, pp. 204–205,
    for the opaque real power-gauge measure. No cube,
    section-nullity or finite-source-measure hypothesis remains. *)
Theorem euclidean_real_power_compact_subset (R : realType) c p :
  (0<c)%R -> (0<p)%R -> forall n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))),
    compact A -> 0<metric_real_power_measure c p A ->
    exists B, [/\ compact B, B `<=` A, 0<metric_real_power_measure c p B & metric_real_power_measure c p B< +oo].
Proof.
move=> hc hp; elim=> [|n IH] A hA hpos.
- pose X := inner_metric_space (@euclidean_inner_productP R 0).
  have hmu := @metric_real_power_measure_specification R X c p.
  have hm := metric_real_power_measure_law (ltW hc) hmu.
  have hsub : A `<=` [set (0%R : X)].
    move=> x hx; apply/ffunP=> i; have hi := ltn_ord i; by rewrite ltn0 in hi.
  have hb := le_trans (measure_mono hm hsub) (@real_power_singleton_bound R X c p _ 0%R hmu (ltW hc)).
  exists A; split=> //; exact: le_lt_trans hb (ltry _).
- pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
  have hmu := @metric_real_power_measure_specification R X c p.
  have hm := metric_real_power_measure_law (ltW hc) hmu.
  case: (pselect (exists (l : 'I_n.+1) (t : R),
      0<metric_real_power_measure c p (A `&` [set x | x l=t])))=> [hex|hno].
  + have [l [t ht]] := hex.
    exact: (@compact_positive_coordinate_section_reduction R n c p A l t (ltW hc) (ltW hp) IH hA ht).
  + have hnull (l : 'I_n.+1) (t : R) : metric_real_power_measure c p (A `&` [set x | x l=t])=0.
      apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
      apply/negP=> ht; apply: hno; by exists l,t.
    exact: (@compact_null_sections_finite_positive_subset R n.+1 c p _ A hmu (ltn0Sn n) hc hp hA hnull hpos).
Qed.

(** Source for [metric_real_power_compact_finite_positive_subset]:
    abstract-interface version of 2.10.47, pp. 204–205.
    Every measure satisfying the power-gauge laws has the
    property, by uniqueness; the opaque selected measure
    is not an additional hypothesis on the caller. *)
Theorem metric_real_power_compact_finite_positive_subset (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_metric_real_power_measure c p mu -> (0<c)%R -> (0<p)%R -> compact A -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hc hp hA hpos.
have he T := metric_real_power_measure_unique hmu
  (@metric_real_power_measure_specification R (inner_metric_space (@euclidean_inner_productP R n)) c p) T.
rewrite he in hpos.
have [B [hBc hBA hBp hBf]] := @euclidean_real_power_compact_subset R c p hc hp n A hA hpos.
exists B; split=> //; by rewrite he.
Qed.
