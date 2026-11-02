(** Federer (1969), 3.2.12, pp. 249–250: the
    characteristic approximation needs measurable fibre sets
    almost everywhere, obtained from 2.10.26 and countable
    finite source exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  HausdorffMeasure MappingMultiplicity FiniteCoareaFibreMeasurability LipschitzUP
  CountablyMeasurableUP CountablyMeasurableSubsets MeasureUP MeasureSplit MeasureCountableClosure
  MeasureAlmostUP MeasureAlmostBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_source_fibre_measurable_almost]: the
    measurable characteristic fibres in the approximation
    proof of Federer 3.2.12, p. 250.
    Infinite measurable source mass is allowed; no Borel
    or fibre-measurability assumption is added. *)
Theorem coarea_source_fibre_measurable_almost (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<=m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n)) (mapping_fibre f A y)].
Proof.
move=>hnm hf hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hb:=@hausdorff_measure_is_measure R X (m-n).
have hCount:=@measurable_subset_countably_measurable R X mu hm A setT hA (fun x _=>Logic.I)
  (euclidean_lebesgue_countably_measurable R m).
have [C [hC [hUnion hFinite]]]:=hCount.
have hPieces B:C B ->measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|measure_measurable (@hausdorff_measure R X (m-n)) (mapping_fibre f B y)].
  move=>hB; exact ((finite_coarea_fibre_measurability hnm hf (hFinite B hB).1 (hFinite B hB).2).2).
have hAll:=@measure_almost_everywhere_countable R [the choiceType of Y] [the choiceType of set X]
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) C
  (fun B=>[set y|measure_measurable (@hausdorff_measure R X (m-n)) (mapping_fibre f B y)]) hC hPieces.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _ hAll)=>y hy.
change (measure_measurable (@hausdorff_measure R X (m-n)) (mapping_fibre f A y)).
have hEq:mapping_fibre f A y=\bigcup_(B in C) mapping_fibre f B y.
  rewrite hUnion; apply/seteqP; split=>x.
  - move=>[[B hB hx] he]; exists B=> //; by split.
  - move=>[B hB [hx he]]; split=> //; by exists B.
rewrite hEq; exact (measure_measurable_countable_union hb hC (fun B hB=>hy B hB)).
Qed.
