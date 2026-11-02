(** Supporting Federer (1969), 2.10.46, p. 204, and Freilich (1950), Theorem
    4.5, Parts 1–5, pp. 242–247: the scalar-first Euclidean block chart
    preserves Lebesgue product measure. This is a consequence of 2.6.5, pp.
    119–120, and an adapted orthogonal chart's exposed laws, not a new
    selected construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanLebesgueDimensions EuclideanLebesgueBijections EuclideanLebesgueLinear
  LebesgueScalarMeasure MeasureUP MeasureBijectionUP MeasureBijectionLaws ProductMeasure
  OrthogonalProjectionChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_block_measure_bijection]: supporting
    scalar-first coordinate form of 2.6.5, p. 120,
    for the Fubini step in 2.10.46, p. 204.
    Empty transverse coordinate blocks are included. *)
Lemma scalar_block_measure_bijection (R : realType) n :
  is_measure_bijection (@euclidean_lebesgue_measure R (1+n))
    (product_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R n))
    (fun z=>(euclidean_one_project (@euclidean_block_split R 1 n z).1,
      (@euclidean_block_split R 1 n z).2))
    (fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)).
Proof.
have hb : is_measure_bijection (@euclidean_lebesgue_measure R (1+n))
    (product_measure (euclidean_lebesgue_is_measure R 1) (euclidean_lebesgue_is_measure R n))
    (@euclidean_block_split R 1 n) (@euclidean_block_join R 1 n).
  constructor; [exact: euclidean_block_splitK | exact: euclidean_block_joinK | exact: euclidean_block_measure].
have hl : is_measure_bijection (@euclidean_lebesgue_measure R 1) (@lebesgue_scalar_measure R)
    (@euclidean_one_project R) (@euclidean_one_embed R) := positive_euclidean_line_bijection R.
have hp := @measure_bijection_product R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  [the choiceType of real_line_metric R]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  _ _ _ _ (euclidean_lebesgue_is_measure R 1) (euclidean_lebesgue_is_measure R n)
  (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R n)
  _ _ _ _ hl (measure_bijection_identity (@euclidean_lebesgue_measure R n)).
exact: measure_bijection_compose hb hp.
Qed.

(** Source for [scalar_projection_chart_measure_bijection]:
    supporting adapted scalar-first chart in 2.10.46,
    p. 204; Freilich (1950), Theorem 4.5,
    Parts 1–5, pp. 242–247. Orthogonal invariance
    and the abstract chart equations give the measure law. *)
Lemma scalar_projection_chart_measure_bijection (R : realType) k
    (p : {linear R_n R (1+k) -> R_n R k})
    (c d : {linear R_n R (1+k) -> R_n R (1+k)}) :
  is_orthogonal_projection_chart p c d ->
  is_measure_bijection (@euclidean_lebesgue_measure R (1+k))
    (product_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R k))
    (fun z=>(euclidean_one_project (@euclidean_block_split R 1 k (c z)).1,
      (@euclidean_block_split R 1 k (c z)).2))
    (fun z=>d (@euclidean_block_join R 1 k (euclidean_one_embed z.1,z.2))).
Proof.
move=> hc.
have ho : is_measure_bijection (@euclidean_lebesgue_measure R (1+k))
    (@euclidean_lebesgue_measure R (1+k)) c d.
  constructor.
  - exact: projection_chart_forward_inverse_law hc.
  - exact: projection_chart_backward_inverse_law hc.
  - apply: funext=> A; exact: euclidean_orthogonal_pushforward (projection_chart_orthogonal_law hc) A.
exact: measure_bijection_compose ho (scalar_block_measure_bijection R k).
Qed.
