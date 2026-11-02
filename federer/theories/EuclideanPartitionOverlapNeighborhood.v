(** Federer (1969), 3.1.13, pp. 224–225:
    the finite overlap family S_x is valid
    throughout a neighbourhood of x, so it
    can be used for actual differentiation of
    the locally finite bump sum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  FiniteNormEquivalence NormDifferentialUP NormBoundedLinearTopology EuclideanInnerProduct
  MetricClosedBalls FedererCoverRadius LipschitzRadiusOverlap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_open_norm_domain]:
    the usual open-set convention agrees with
    the norm-neighbourhood convention in the partition
    construction, Federer 3.1.13, pp. 224–225. *)
Lemma inner_open_norm_domain (R : realType) (X : lmodType R)
    (B : X->X->R) (hB : is_inner_product B) (U : set X) :
  @open [the topologicalType of inner_metric_space hB] U ->
  forall a, U a -> norm_domain_interior (inner_norm hB) U a.
Proof.
move=>ho a ha.
apply: (norm_domain_interior_neighbourhood (inner_norm_real_norm hB) U a).2.
apply: (inner_real_norm_same_nbhs hB a U).1.
by move:ho; rewrite openE; apply.
Qed.

(** Source for [partition_overlap_neighborhood]:
    the open ball about x of radius
    10h(x), restricted to the cover union,
    is a neighbourhood meeting only the
    selected balls indexed by S_x, Federer
    3.1.13, pp. 224–225. *)
Definition partition_overlap_neighborhood (R : realType) m
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (x : inner_metric_space (@euclidean_inner_productP R m)) :=
  (\bigcup_(T in Phi) T) `&`
    [set y | mdist x y<10*federer_cover_radius Phi x].

(** Source for [partition_overlap_neighborhood_laws]:
    the same finite index family S_x
    works on an open neighbourhood, supporting
    D^i sigma=sum_s D^i u_s in
    Federer 3.1.13, p. 225. *)
Theorem partition_overlap_neighborhood_laws (R : realType) m
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m))) x :
  (forall T, Phi T -> open T) -> (\bigcup_(T in Phi) T) x ->
  partition_overlap_neighborhood Phi x x /\
  (forall y, partition_overlap_neighborhood Phi x y -> (\bigcup_(T in Phi) T) y) /\
  (forall y, partition_overlap_neighborhood Phi x y ->
    norm_domain_interior (inner_norm (@euclidean_inner_productP R m))
      (partition_overlap_neighborhood Phi x) y) /\
  forall s y, S s -> partition_overlap_neighborhood Phi x y ->
    metric_closed_ball s (10*federer_cover_radius Phi s) y ->
    lipschitz_radius_overlap S (federer_cover_radius Phi) 10 10 x s.
Proof.
move=>ho hx.
have hu : open (\bigcup_(T in Phi) T) by apply: bigcup_open=>T hT; exact: (ho T hT).
have hp : 0<federer_cover_radius Phi x.
  apply: (federer_cover_radius_positive ho); have [T hT hxT] := hx; by exists T.
have hball : open [set y | mdist x y<10*federer_cover_radius Phi x].
  exact: metric_open_ball_open.
have hopen : open (partition_overlap_neighborhood Phi x) := openI hu hball.
split.
- split; first exact hx; rewrite /= mdistxx; apply: mulr_gt0; [by rewrite ltr0n|exact hp].
split; first by move=>y [hy _].
split; first exact: (inner_open_norm_domain hopen).
move=>s y hs [hy hxy] hsy; split; first exact hs.
exists y; split; first exact: (ltW hxy); exact hsy.
Qed.
