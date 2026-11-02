(** Federer (1969), 3.2.5, pp. 244–245: discard
    the image of the nonpositive or undefined Jacobian locus
    before applying characteristic approximation. This expands
    the rank and null-set reductions in 3.2.3–3.2.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  LipschitzUP MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic TopologicalBorel HausdorffMeasure
  BorelAreaSelection DifferentialRankLociBorel EuclideanLipschitzClassZero
  InjectiveDifferentialPieceUP AreaBorelReductionUP MeasurableAreaBorelReduction Jacobian EuclideanJacobianMeasurable PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_jacobian_locus_borel]: the Borel
    positive-rank locus used in the reduction of Federer
    3.2.5, pp. 244–245. This uses the actual differential
    cover of 3.2.2 and the exact Jacobian of 3.2.1. *)
Lemma positive_jacobian_locus_borel (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (positive_euclidean_jacobian_locus f).
Proof.
move=>hLip; rewrite positive_jacobian_injective_locus.
exact (injective_differential_locus_borel (euclidean_lipschitz_norm_class_zero hLip)).
Qed.

(** Source for [nonpositive_jacobian_image_null]: the negligible
    discarded image in Federer 3.2.5, pp. 244–245,
    using the two cases and Rademacher reduction of 3.2.3,
    pp. 243–244. The complement includes points where
    the actual differential is undefined; no Jacobian value
    is assigned at those points. *)
Theorem nonpositive_jacobian_image_null (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (f @` (~` positive_euclidean_jacobian_locus f))=0.
Proof.
move=>hLip.
have hWhole:=measure_measurable_whole (euclidean_lebesgue_is_measure R m).
have [C [hC [hCA [hCLocus [hNu hNull]]]]]:=measurable_injective_area_subset hLip hWhole.
apply:(@measure_null_subset R _ _ (@hausdorff_measure_is_measure R _ m)
  (f @` (~` positive_euclidean_jacobian_locus f)) (f @` (setT `\` C)) _ hNull).
move=>y [x hx hxy]; exists x; last exact hxy.
split; first exact:I.
move=>hCx; apply:hx; rewrite positive_jacobian_injective_locus; exact (hCLocus x hCx).
Qed.

(** Source for [extended_jacobian_zero_outside_positive_locus]:
    the zero-Jacobian reduction in Federer 3.2.5,
    pp. 244–245. A defined nonnegative Jacobian outside
    its actual positive locus is zero; undefined values
    remain absent from the statement. *)
Lemma extended_jacobian_zero_outside_positive_locus (R:realType) m n
    (f:R_n R m->R_n R n) x j:
  ~positive_euclidean_jacobian_locus f x ->
  partial_function_graph (extended_euclidean_jacobian f) x j -> j=0.
Proof.
move=>hNot [r [hr <-]].
have hNonneg:(0<=r)%R:=euclidean_jacobian_nonnegative hr.
have hLe:(r<=0)%R.
  rewrite leNgt; apply/negP=>hPos; apply:hNot; exists r; by split.
have hr0:r=0%R by apply/eqP; rewrite eq_le hLe hNonneg.
by rewrite hr0.
Qed.
