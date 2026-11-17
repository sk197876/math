(** Supporting the Euclidean-factor product argument in
    Federer (1969), 3.2.45, p. 280. Reuse the
    restriction, image and isometry laws already used
    in the product proof of 2.10.45, pp. 202–203. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCartesianMap EuclideanBlockCoordinates EuclideanMetricProduct EuclideanSquaredProduct
  EuclideanProductTranslation HausdorffProductSliceTranslation
  IntegralGeometricMeasure ConvexIntegralGeometricIsometricEmbedding
  MeasureUP MeasureRestriction MeasurePushforward PushforwardMeasurableSets
  MetricProductRectangles MetricCartesianProductUP NormMetricScaleContinuity
  ContinuousBorelPreimages TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_product_slice_is_measure]:
    supporting first-factor measure for Federer 3.2.45,
    p. 280. The original Q_1 mass of U times V,
    with fixed arbitrary V, is a measure on U.
    This reuses restriction and image measures from
    2.1.2, p. 54; no measurability of V is added. *)
Theorem convex_geometric_product_slice_is_measure (R : realType) m n k (hKN : (k <= n)%N)
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure (fun U : set (inner_metric_space (@euclidean_inner_productP R m)) =>
    @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
      (euclidean_cartesian_set U V)).
Proof.
pose mu := @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1.
have hMu := @convex_integral_geometric_measure_is_measure R (m+n) (m+k)
  (leq_add (leqnn m) hKN) 1 (lexx 1).
have hFunction : (fun U : set (inner_metric_space (@euclidean_inner_productP R m)) =>
    mu (euclidean_cartesian_set U V)) =
    measure_pushforward (fun z => (@euclidean_block_split R m n z).1)
      (measure_restrict mu ((fun z => (@euclidean_block_split R m n z).2) @^-1` V)).
  apply: funext=> U; rewrite /measure_pushforward /measure_restrict setIC.
  reflexivity.
rewrite hFunction.
exact: measure_pushforward_is_measure (measure_restrict_is_measure hMu _).
Qed.

(** Source for [convex_geometric_product_slice_borel_measurable]:
    supporting Borel measurability in the Haar step of
    Federer 3.2.45, p. 280. The first projection is
    continuous, so Borel cylinders are measurable for
    the original Q_1; restricting by arbitrary V preserves
    their measurability. No regularity of the full slice
    measure on arbitrary sets is assumed. *)
Theorem convex_geometric_product_slice_borel_measurable (R : realType) m n k (hKN : (k <= n)%N)
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (U : set (inner_metric_space (@euclidean_inner_productP R m))) :
  borel_set U -> measure_measurable
    (fun B => @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
      (euclidean_cartesian_set B V)) U.
Proof.
move=> hU.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose mu := @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1.
have hMu := @convex_integral_geometric_measure_is_measure R (m+n) (m+k)
  (leq_add (leqnn m) hKN) 1 (lexx 1).
have hFunction : (fun B : set X => mu (euclidean_cartesian_set B V)) =
    measure_pushforward (fun z => (@euclidean_block_split R m n z).1)
      (measure_restrict mu ((fun z => (@euclidean_block_split R m n z).2) @^-1` V)).
  apply: funext=> B; rewrite /measure_pushforward /measure_restrict setIC; reflexivity.
rewrite hFunction.
apply: pushforward_measurable_from_preimage; apply: measure_restrict_measurable.
apply: (borel_regular_borel_measurable hMu
  (@convex_integral_geometric_measure_borel_regular R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (lexx 1))).
have hProjection := metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R m n).
have hContinuous : continuous (fun z : Z => ((@euclidean_block_split R m n z).1 : X)).
  apply: (@metric_fixed_lipschitz_continuous R [the metricType R of Z] [the metricType R of X]
    (fun z => (euclidean_block_split z).1) 1%R hProjection.1)=> z w.
  exact: hProjection.2 z w I I.
exact: (@continuous_borel_preimage [the topologicalType of Z] [the topologicalType of X]
  (fun z => (euclidean_block_split z).1) hContinuous U hU).
Qed.

(** Source for [convex_geometric_product_slice_translation]:
    supporting translation invariance for Federer 3.2.45,
    p. 280. The actual coordinate translation of the
    product is an isometry. Reuse the all-set Q_1
    isometric-embedding theorem of 3.2.36, p. 273.
    Both factors remain arbitrary. *)
Theorem convex_geometric_product_slice_translation (R : realType) m n k (hKN : (k <= n)%N)
    (a : inner_metric_space (@euclidean_inner_productP R m))
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set ((fun x => (a+x)%R) @` U) V) =
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set U V).
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose pair := fun x : X => fun y : Y => euclidean_block_join (x,y).
pose first := fun z : Z => (@euclidean_block_split R m n z).1.
pose second := fun z : Z => (@euclidean_block_split R m n z).2.
have hProduct := @euclidean_blocks_are_squared_metric_product R m n.
have hRectangle := @euclidean_product_translation_rectangle R m [the metricType R of Z]
  [the metricType R of Y] pair first second hProduct a U V.
have hInvariant := @convex_integral_geometric_isometric_embedding R (m+n) (m+n) (m+k)
  (leq_add (leqnn m) hKN) (leq_add (leqnn m) hKN)
  (euclidean_product_translation pair first second a)
  (@euclidean_product_translation_isometry R m [the metricType R of Z] [the metricType R of Y]
    pair first second hProduct a) (euclidean_cartesian_set U V).
rewrite hRectangle in hInvariant.
exact hInvariant.
Qed.
