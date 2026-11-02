(** Federer (1969), 3.2.21, p. 257: every
    positive restricted-Jacobian section over the purely unrectifiable
    Borel target is null, hence so is the ambient locus. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanSliceDifferentials
  EuclideanLebesgueDimensions EuclideanBlockNullSections MeasureUP MeasureBasic MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel LipschitzUP RectifiableSetUP HausdorffMeasure
  Jacobian EuclideanLinearJacobian BorelAreaSelection PositiveRestrictedDifferentialLocus
  PureUnrectifiableEqualDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pure_unrectifiable_slice_positive_locus_null]:
    the Fubini contradiction in Federer 3.2.21, p. 257.
    At each actual full differentiability point, restricting to
    the mu-coordinate slice gives its actual differential.
    The equal-dimension area argument therefore annihilates the
    entire positive-Jacobian section. Erratum p. 5, book
    p. 257 line 26: the section mass is L^mu(B). *)
Lemma pure_unrectifiable_slice_positive_locus_null (R:realType) k mu n
    (f:inner_metric_space (@euclidean_inner_productP R (k+mu))->
      inner_metric_space (@euclidean_inner_productP R n))
    (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_metric_lipschitz setT f ->borel_set T ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu T ->
  @euclidean_lebesgue_measure R (k+mu)
    (positive_restricted_differential_locus f (@euclidean_last_injection_map R k mu) T)=0%E.
Proof.
move=>hLip hT hPure.
apply:euclidean_block_null_sections.
- apply:(@borel_regular_borel_measurable R _ _ (euclidean_lebesgue_is_measure R (k+mu))
    (euclidean_lebesgue_borel_regular R (k+mu))).
  exact:(@positive_restricted_differential_locus_borel R (k+mu) n mu f
    (@euclidean_last_injection_map R k mu) T hLip hT).
- move=>y; pose fy:=fun z:R_n R mu=>f (euclidean_block_join (y,z)).
  have hFy:=euclidean_slice_lipschitz hLip y.
  have hNull:=pure_unrectifiable_equal_dimension_positive_locus_null hFy hPure.
  apply:(measure_null_subset (euclidean_lebesgue_is_measure R mu) _ hNull)=>z [hTz [D [hD hPos]]].
  split; last exact hTz.
  exists (euclidean_linear_jacobian mu (hom_comp D (@euclidean_last_injection_map R k mu))).
  split; last exact hPos.
  apply:(euclidean_jacobian_graph mu setT fy z _).2.
  exists (hom_comp D (@euclidean_last_injection_map R k mu)); split; last reflexivity.
  exact:(euclidean_slice_differential hD).
Qed.
