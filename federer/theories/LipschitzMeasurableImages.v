(** Federer (1969), 3.2.5, pp. 244–245: images
    of measurable source subsets are Hausdorff measurable,
    and represented images are countably Hausdorff measurable.
    These support the three alternative measurability conditions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanMetricCompleteness EuclideanMetricSeparability NormMetricScaleContinuity LipschitzUP
  EuclideanHausdorffLebesgue HausdorffMeasure HausdorffClosedCoverAgreement HausdorffLipschitzImages
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostBasic
  TopologicalBorel BorelRegularMeasureUP InjectiveBorelImage BorelAreaSelection
  CountablyMeasurableUP CountablyMeasurableSubsets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_lipschitz_measurable_image]: measurability
    of f(W) in the last paragraph of Federer 3.2.5,
    p. 245. The stronger full measurable-image assertion
    follows directly from the Borel univalent selection of
    3.2.4 and its null image deficit. *)
Theorem euclidean_lipschitz_measurable_image (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (f @` A).
Proof.
move=>hLip hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
have hb:=@hausdorff_measure_is_measure R Y m.
have [B [hB [hBA [hInj hNull]]]]:=euclidean_borel_area_selection hLip hA.
have [M [hM hBound]]:=hLip.
have hCont:continuous f.
  apply:(@metric_fixed_lipschitz_continuous R X Y f M (ltW hM)).
  by move=>x y; exact (hBound.2 x y I I).
have hIB:@borel_set Y (f @` B):=@injective_borel_image_borel R X Y f B
  (@euclidean_metric_complete R m) (@euclidean_metric_separable R m)
  (@metric_hausdorff R Y) hCont hB hInj.
have hImageMeas:measure_measurable beta (f @` B):=
  borel_regular_borel_measurable hb (@hausdorff_measure_borel_regular R Y m) hIB.
have hDecomp:f @` A=(f @` B) `|` ((f @` A) `\` (f @` B)).
  apply/seteqP; split=>y.
  - move=>hy; case:(pselect ((f @` B) y))=>hBy; first by left.
    right; by split.
  - move=>[[x hx hxy]|[hy _]]; last exact hy.
    exists x; first exact ((hBA x hx).1); exact hxy.
rewrite hDecomp; exact (measure_measurable_union hb hImageMeas (measure_null_measurable hb hNull)).
Qed.

(** Source for [euclidean_lipschitz_countably_measurable_image]:
    the countable Hausdorff-measurability of f(A) used in
    Federer 3.2.5, p. 245. Cover A by countably
    many finite Lebesgue-measure sets and use 2.10.11
    on their images; no global sigma-finiteness of H^m
    on the target ambient space is assumed. *)
Theorem euclidean_lipschitz_countably_measurable_image (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_countably_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (f @` A).
Proof.
move=>hLip hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R Y m.
have hm:=euclidean_lebesgue_is_measure R m.
have [F [hF [hUnion hFinite]]]:=@measurable_subset_countably_measurable R X mu hm A setT hA
  (fun x _=>I) (euclidean_lebesgue_countably_measurable R m).
pose G:=(fun B:set X=>f @` B) @` F.
exists G; split.
- exact (sub_countable (card_image_le _ _) hF).
split.
- apply/seteqP; split=>y.
  + move=>[x hx hxy]; rewrite hUnion in hx; have [B hB hxB]:=hx.
    exists (f @` B); first by exists B.
    by exists x.
  + move=>[C [B hB <-] [x hx hxy]]; exists x; last exact hxy.
    rewrite hUnion; by exists B.
- move=>C [B hB <-]; split; first exact (euclidean_lipschitz_measurable_image hLip (hFinite B hB).1).
  have [M [hM hBound]]:=hLip.
  have hImageBound:=hausdorff_lipschitz_image_bound m hBound B.
  rewrite (euclidean_hausdorff_spherical_lebesgue B).1 in hImageBound.
  apply:(le_lt_trans hImageBound).
  have hNum:mu B \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm B)); exact (hFinite B hB).2.
  change (is_true ((M^+m)%R%:E*mu B< +oo)).
  by rewrite -(fineK hNum) -EFinM ltry.
Qed.
