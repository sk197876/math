(** Federer (1969), 4.1.2, p. 347: the Euclidean-space
    times real-line measure needed for the reflexive input's
    coordinate Fubini argument. Existing countable bases and
    the original open-set measurability prove every Borel premise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness EuclideanNormCountableBase EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext RealMetricBackground RealLineSeparability
  SeparableMetricBaseSealed LebesgueScalarMeasure BorelRegularMeasureUP
  MeasureUP ProductMeasure ProductBorelRectangles MeasurableBorelFamily TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_line_product_borel_measurable]: the product
    Borel sets used to transfer the original one-dimensional
    theorem 2.9.22 to D_j f in Federer 4.1.2, p. 347.
    The zero-dimensional Euclidean factor is retained. *)
Theorem euclidean_line_product_borel_measurable (R:realType) n
    (A:set (R_n R n*R)):
  @borel_set ((real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    * (real_line_metric R))%type A ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R n)
    (lebesgue_scalar_is_measure R)) A.
Proof.
pose X:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose Y:=real_line_metric R.
have[U hU]:=@euclidean_norm_countable_open_base R n.
have[D [hDc hDd]]:=@real_line_countable_dense R.
pose V:=@SeparableMetricBase.value R Y D hDc hDd.
pose hV:=@SeparableMetricBase.laws R Y D hDc hDd.
have hOpen:=@product_open_sets_measurable R [the topologicalType of X]
  [the topologicalType of Y] (@euclidean_lebesgue_measure R n) (@lebesgue_scalar_measure R)
  (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R) U V hU hV
  (@euclidean_distribution_measure_open R n)
  (borel_regular_open_measurable (lebesgue_scalar_borel_regular R)).
exact:(@open_measurable_implies_borel_measurable R [the topologicalType of (X*Y)%type]
  (product_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R))
  (product_measure_is_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)) hOpen A).
Qed.
