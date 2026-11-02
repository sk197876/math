(** Federer (1969), 3.2.32, p. 270: supporting
    source restrictions above Borel target pieces. Continuity
    proves the source measurability needed for 3.2.22. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  NormMetricScaleContinuity MeasureUP MeasureFiniteClosure HausdorffMeasure HausdorffClosedCoverAgreement
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages RectifiableSetUP MeasureRectifiableSubset
  MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_borel_target_piece]: supporting the
    application of 3.2.22 in Federer 3.2.32, p. 270.
    A Borel target inverse image intersected with the finite
    measurable original source is measurable and finite rectifiable.
    No general preimage assertion for completed target sets is used. *)
Lemma rectifiable_borel_target_piece (R:realType) m n v
    (W:set (R_n R n)) (F:R_n R n->R_n R v) (D:set (R_n R v)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) D ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (W `&` F @^-1` D) /\
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m (W `&` F @^-1` D).
Proof.
move=>hRect hW [L [hL hLip]] hD.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
have hH:=@hausdorff_measure_is_measure R X m.
have hCont:continuous (F:X->Y).
  apply:(metric_fixed_lipschitz_continuous (ltW hL))=>x y; exact:(hLip.2 x y Logic.I Logic.I).
split.
- apply:(measure_measurable_intersection hH hW).
  exact:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m)
    (continuous_borel_preimage hCont hD)).
- apply:(@measure_rectifiable_subset R X (@hausdorff_measure R X m) m W _ _ hRect).
  by move=>x [hx _].
Qed.

(** Source for [mapping_fibre_target_piece]: exact fibre restriction
    supporting Federer 3.2.32, p. 270. Above D the
    restricted fibre is the entire original fibre; outside D
    it is empty. This is a set identity, not a measure premise. *)
Lemma mapping_fibre_target_piece (X Y:Type) (W:set X) (F:X->Y) (D:set Y) y:
  mapping_fibre F (W `&` F @^-1` D) y=
    (if pselect (D y) then mapping_fibre F W y else set0).
Proof.
case:pselect=>hy; apply/seteqP; split=>x.
- move=>[[hx hDx] hFx]; by split.
- move=>[hx hFx]; split; last exact hFx.
  split=>//; change (D (F x)); change (F x=y) in hFx; by rewrite hFx.
- move=>[[hx hDx] hFx]; exfalso; apply:hy.
  change (F x=y) in hFx; by rewrite -hFx.
- by [].
Qed.
