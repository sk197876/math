(** Supporting parameter space for Federer (1969), 2.10.4, p. 172. The same
    O*(n,m) as in 1.7.4, pp. 30–31, carries its existing compact relative
    Hom topology from 2.7.16(6), p. 139. Derive compactness from the proved
    orthogonal-group restriction, without assuming a group structure or a
    selected projection as extra hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric Hom CoordinateProjection EuclideanOrthogonalInvariantMeasures
  OrthogonalInjectionSpaces OrthogonalGroupTopology ProjectionNorm NormMetricScaleContinuity
  HomInner HomSpaceTopology IsotropyGroupTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_projection_space]: supporting
    topological parameter presentation of O*(n,m) in
    Federer 2.10.4, p. 172, with the topology
    already used for 2.7.16(6), p. 139. *)
Definition euclidean_projection_space (R : realType) (n m : nat) : topologicalType :=
  [the topologicalType of set_type (euclidean_orthogonal_projections R n m)].

(** Source for [euclidean_projection_linear]: supporting
    linear-map presentation of a parameter in the
    supremum of Federer 2.10.4, p. 172. *)
Definition euclidean_projection_linear (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m) : {linear R_n R n -> R_n R m} :=
  hom_as_linear (orthogonal_projection_map p).

(** Source for [euclidean_projection_linear_member]: supporting
    identification of the topological parameters with
    the printed O* family of Federer 2.10.4, p. 172. *)
Lemma euclidean_projection_linear_member (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m) : O_star (euclidean_projection_linear p).
Proof. exact: (O_star_projection _).2 (orthogonal_projection_map_projection p). Qed.

(** Source for [euclidean_projection_linear_complete]: supporting
    reverse identification for Federer 2.10.4, p. 172.
    Every projection in the printed supremum is represented
    in the same compact parameter space. *)
Lemma euclidean_projection_linear_complete (R : realType) (n m : nat)
    (p : {linear R_n R n -> R_n R m}) : O_star p ->
  exists q : euclidean_projection_space R n m, forall x, euclidean_projection_linear q x=p x.
Proof.
move=> hp.
exists (orthogonal_projection_of (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R n) ((O_star_projection p).1 hp)).
by move=> x.
Qed.

(** Source for [euclidean_projection_space_compact]: supporting
    compactness of O*(n,m), from Federer 2.7.16(6),
    p. 139, for the uniform generator enlargement
    needed in 2.10.4(2), p. 172. No chosen
    group operations or nonempty-space premise is added. *)
Theorem euclidean_projection_space_compact (R : realType) (n m : nat) :
  compact [set: euclidean_projection_space R n m].
Proof.
have [mulS [invS [eS hS]]] := @orthogonal_group_restriction_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
exact (@orthogonal_projections_compact R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) n (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) mulS invS eS hS).
Qed.

(** Source for [euclidean_projection_nonexpanding]: supporting
    contraction estimate for the neighbourhoods used in
    Federer 2.10.4(2), p. 172, from the projection
    norm estimate of 1.7.7, p. 34. *)
Lemma euclidean_projection_nonexpanding (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m)
    (x y : inner_metric_space (@euclidean_inner_productP R n)) :
  mdist (euclidean_projection_linear p x : inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p y)<=mdist x y.
Proof.
rewrite !inner_metric_distanceE -linearB.
exact (@orthogonal_projection_norm_bound R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (euclidean_projection_linear p) (orthogonal_projection_map_projection p) (x-y)).
Qed.

(** Source for [euclidean_projection_continuous]: supporting
    continuity of each image map in Federer 2.10.4,
    p. 172, from its proved contraction property.
    The Euclidean metric is retained on both spaces. *)
Lemma euclidean_projection_continuous (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m) :
  continuous (euclidean_projection_linear p : inner_metric_space (@euclidean_inner_productP R n) ->
    inner_metric_space (@euclidean_inner_productP R m)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 (ler01 : (0:R)<=1))=> x y.
rewrite mul1r; exact: euclidean_projection_nonexpanding.
Qed.

(** Source for [euclidean_projection_evaluation_continuous]:
    supporting joint continuity of (p,x) mapping to
    p(x) for Federer 2.10.4(2), p. 172. Restrict
    the evaluation map on the existing Hom normed space;
    no continuity of a volume supremum is assumed. *)
Theorem euclidean_projection_evaluation_continuous (R : realType) (n m : nat) :
  continuous (fun z : euclidean_projection_space R n m *
      inner_metric_space (@euclidean_inner_productP R n) =>
    (euclidean_projection_linear z.1 z.2 : inner_metric_space (@euclidean_inner_productP R m))).
Proof.
pose P := euclidean_projection_space R n m.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose H := inner_metric_space (hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R m) (@coordinate_basisP R n)).
have hi : continuous (fun z : P*E => ((set_val z.1 : H),z.2)).
  apply: topological_pair_continuous; last exact: second_projection_continuous.
  move=> z; exact: continuous_comp (@first_projection_continuous P E z)
    (@set_type_val_continuous H (euclidean_orthogonal_projections R n m) z.1).
move=> z; exact: continuous_comp (hi z)
  (@hom_evaluation_continuous R (R_n R n) (R_n R m)
    (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
    n (@coordinate_basis R n) (@coordinate_basisP R n) ((set_val z.1 : H),z.2)).
Qed.

(** Source for [euclidean_projected_compact_image]: supporting
    compact projected generators for Federer 2.10.4(2),
    p. 172, by continuity of each orthogonal projection. *)
Lemma euclidean_projected_compact_image (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> compact (euclidean_projection_linear p @` K :
    set (inner_metric_space (@euclidean_inner_productP R m))).
Proof.
move=> hK; apply: continuous_compact hK.
exact: continuous_subspaceT (@euclidean_projection_continuous R n m p).
Qed.
