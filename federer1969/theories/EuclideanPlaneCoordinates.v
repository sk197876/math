(** The usual two scalar coordinates on R^2 in Federer (1969), 2.5.10, p.
    101, and its Cartesian Lebesgue measure in 2.6.5, pp. 119–120. This
    homeomorphism connects the existing dot-product Euclidean space with the
    Cartesian pair of real lines. It does not replace the Euclidean metric
    by the auxiliary product metric used to express completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground MetricProductBackground EuclideanOneCoordinate EuclideanCoordinateSplit
  EuclideanCoordinateTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_plane_join]: the scalar
    coordinate pair (x1,x2) of the Euclidean plane
    in Federer 2.5.10, p. 101, expressed
    in the existing finite coordinate space. *)
Definition euclidean_plane_join (R : realType)
    (p : metric_product [the metricType R of real_line_metric R]
      [the metricType R of real_line_metric R]) :
    inner_metric_space (@euclidean_inner_productP R 2) :=
  @euclidean_join R 1 (euclidean_one_embed p.2,p.1).

(** Source for [euclidean_plane_split]: inverse scalar
    coordinates for the plane in Federer 2.5.10,
    p. 101, and the product of 2.6.5,
    pp. 119–120. *)
Definition euclidean_plane_split (R : realType)
    (x : inner_metric_space (@euclidean_inner_productP R 2)) :
    metric_product [the metricType R of real_line_metric R]
      [the metricType R of real_line_metric R] :=
  ((euclidean_split x).2,euclidean_one_project (euclidean_split x).1).

(** Source for [euclidean_plane_joinK]: inverse coordinate
    identity supporting Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_joinK (R : realType) :
  cancel (@euclidean_plane_join R) (@euclidean_plane_split R).
Proof. by move=> [s t]; rewrite /euclidean_plane_split /euclidean_plane_join euclidean_joinK /= euclidean_one_embedK. Qed.

(** Source for [euclidean_plane_splitK]: inverse coordinate
    identity supporting Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_splitK (R : realType) :
  cancel (@euclidean_plane_split R) (@euclidean_plane_join R).
Proof.
move=> x; rewrite /euclidean_plane_join /euclidean_plane_split euclidean_one_projectK.
have he : ((euclidean_split x).1,(euclidean_split x).2)=euclidean_split x by case: (euclidean_split x).
by rewrite he euclidean_splitK.
Qed.

(** Source for [euclidean_plane_join_continuous]: topology
    compatibility of the Cartesian identification in Federer
    2.6.5, pp. 119–120, used for the
    Borel images in 2.5.10, p. 101. *)
Lemma euclidean_plane_join_continuous (R : realType) : continuous (@euclidean_plane_join R).
Proof.
have hp : continuous (fun p : metric_product [the metricType R of real_line_metric R]
      [the metricType R of real_line_metric R] => (euclidean_one_embed p.2,p.1)).
  apply: topological_pair_continuous.
  - move=> p; apply: (@continuous_comp (Topological.clone (metric_product [the metricType R of real_line_metric R] [the metricType R of real_line_metric R]) _) (Topological.clone R^o _) (Topological.clone (inner_metric_space (@euclidean_inner_productP R 1)) _) snd (@euclidean_one_embed R) p).
    + exact: second_projection_continuous.
    + exact: euclidean_one_embed_continuous.
  - exact: first_projection_continuous.
move=> p; apply: (@continuous_comp (Topological.clone (metric_product [the metricType R of real_line_metric R] [the metricType R of real_line_metric R]) _) (Topological.clone ((inner_metric_space (@euclidean_inner_productP R 1))*R^o)%type _) (Topological.clone (inner_metric_space (@euclidean_inner_productP R 2)) _) (fun p => (euclidean_one_embed p.2,p.1)) (@euclidean_join R 1) p).
- exact: hp.
- exact: euclidean_join_continuous.
Qed.

(** Source for [euclidean_plane_split_continuous]: inverse
    topology compatibility supporting Federer 2.5.10,
    p. 101, and 2.6.5, pp. 119–120. *)
Lemma euclidean_plane_split_continuous (R : realType) : continuous (@euclidean_plane_split R).
Proof.
apply: topological_pair_continuous.
- move=> x; apply: (@continuous_comp (Topological.clone (inner_metric_space (@euclidean_inner_productP R 2)) _) (Topological.clone ((inner_metric_space (@euclidean_inner_productP R 1))*R^o)%type _) (Topological.clone R^o _) (@euclidean_split R 1) snd x).
  + exact: euclidean_split_continuous.
  + exact: second_projection_continuous.
- move=> x; apply: (@continuous_comp (Topological.clone (inner_metric_space (@euclidean_inner_productP R 2)) _) (Topological.clone (inner_metric_space (@euclidean_inner_productP R 1)) _) (Topological.clone R^o _) (fun x => (euclidean_split x).1) (@euclidean_one_project R) x).
  + apply: (@continuous_comp (Topological.clone (inner_metric_space (@euclidean_inner_productP R 2)) _) (Topological.clone ((inner_metric_space (@euclidean_inner_productP R 1))*R^o)%type _) (Topological.clone (inner_metric_space (@euclidean_inner_productP R 1)) _) (@euclidean_split R 1) fst x).
    * exact: euclidean_split_continuous.
    * exact: first_projection_continuous.
  + exact: euclidean_one_project_continuous.
Qed.
