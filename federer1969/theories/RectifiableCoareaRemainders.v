(** Federer (1969), 3.2.22, pp. 258–259: keep
    both the source-chart remainder R and the target-chart
    remainder Q. Erratum p. 5 adds R on book
    p. 258 lines 20/22 and its null fibres on
    p. 259 lines 3/4. These are distinct remainders. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP HausdorffMeasure HausdorffFibreCutoffs HausdorffFibreMeasurability NullFibresProperSource
  CoareaNullFibres MappingMultiplicity MeasureUP MeasureAlmostUP MeasurableFunctionUP
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_null_source_remainder]:
    the source-chart remainder R added by erratum p. 5,
    book p. 258 lines 20/22 and p. 259 lines 3/4,
    has H^(m-mu)-null fibres for H^mu almost every
    target point. Expand the cited 2.10.25 through the
    proved proper-source null-fibre theorem, with no source
    measurability or positivity assumption. *)
Lemma rectifiable_coarea_null_source_remainder (R:realType) n k m mu
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)) A:
  (mu<=m)%N ->is_metric_lipschitz setT F ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A=0 ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) mu)
    [set z|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (m-mu) (mapping_fibre F A z)=0].
Proof.
move=>hDim [L [hL hBound]] hA.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
have hDegree:@hausdorff_measure R X ((m-mu)+mu) A=0.
  by rewrite (subnK hDim).
exact:(@null_hausdorff_fibres_proper_source R X Y F L A (m-mu) mu
  (@coarea_euclidean_source_proper R n) hBound hDegree).
Qed.

(** Source for [rectifiable_coarea_fibre_measurability]:
    the use of 2.10.26 in Federer 3.2.22,
    p. 259. A finite H^m-measurable source subset
    has a measurable H^(m-mu) fibre-mass function and
    almost every actual fibre is H^(m-mu)-measurable.
    The Euclidean source is proper; no extra target
    regularity or positive dimension is assumed. *)
Lemma rectifiable_coarea_fibre_measurability (R:realType) n k m mu
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)) A:
  (mu<=m)%N ->is_metric_lipschitz setT F ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) A ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A< +oo ->
  is_measure_measurable_function (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) mu)
    (partial_function_total (hausdorff_fibre_mass F A (m-mu))) /\
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) mu)
    [set z|measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (mapping_fibre F A z)].
Proof.
move=>hDim [L [hL hBound]] hA hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
have hAm:measure_measurable (@hausdorff_measure R X ((m-mu)+mu)) A.
  by rewrite (subnK hDim).
have hAf:@hausdorff_measure R X ((m-mu)+mu) A< +oo.
  by rewrite (subnK hDim).
exact:(@hausdorff_fibre_measurability_proper_source R X Y F L A (m-mu) mu
  (@coarea_euclidean_source_proper R n) hBound hAm hAf).
Qed.
