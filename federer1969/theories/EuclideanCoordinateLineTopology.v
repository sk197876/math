(** Supporting topology of the line segments in Federer (1969), 2.5.10, p.
    101, using the Euclidean space of 1.7.1, p. 28. Coordinate-line maps are
    continuous and compact intervals have closed images. These are
    general-topology prerequisites, not separately numbered measure
    assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric RealMetricBackground EuclideanCoordinateMetric EuclideanCoordinateTopology TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_line_continuous]:
    supporting continuity of the coordinate lines in
    Federer 2.5.10, p. 101, by the scalar
    coordinate topology of 1.7.1, p. 28. *)
Lemma euclidean_coordinate_line_continuous (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) :
  continuous (euclidean_coordinate_line i v).
Proof.
apply: euclidean_map_continuous=> j.
have he : (fun t : real_line_metric R => euclidean_coordinate_line i v t j)=
    (fun t => v j+t*(@coordinate_basis R n i j)).
  by apply: funext=> t; rewrite /euclidean_coordinate_line !ffunE.
rewrite he=> t; apply: cvgD; first exact: cvg_cst.
apply: cvgM; [exact: cvg_id|exact: cvg_cst].
Qed.

(** Source for [euclidean_coordinate_segment_closed]:
    supporting closedness of the line-segment tests in
    Federer 2.5.10, p. 101, by compactness of
    a real interval and Hausdorffness of the metric space. *)
Lemma euclidean_coordinate_segment_closed (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (a b : R) :
  closed (euclidean_coordinate_line i v @` `[a,b]).
Proof.
apply: (compact_closed (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])).
apply: continuous_compact _ (@segment_compact R a b).
exact: continuous_subspaceT (@euclidean_coordinate_line_continuous R n i v).
Qed.

(** Source for [euclidean_coordinate_segment_borel]:
    Borelness of the line tests for Federer 2.5.10,
    p. 101, using the closed-set inclusion of
    2.2.1, p. 60. *)
Lemma euclidean_coordinate_segment_borel (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (a b : R) :
  borel_set (euclidean_coordinate_line i v @` `[a,b]).
Proof. exact (@closed_borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
  _ (@euclidean_coordinate_segment_closed R n i v a b)). Qed.
