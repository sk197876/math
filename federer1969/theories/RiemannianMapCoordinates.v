(** Federer (1969), 3.2.46, p. 282: maps between
    the actual chart domains are represented in ordinary
    coordinates, retaining exactly their original partial
    domain. This graph adapter chooses no values outside
    the source chart and supplies no differential field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier PartialFunctionUP
  PartialFunctionExtensionUP PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_coordinates]: the exact
    graph of the same map in the original coordinates,
    supporting 3.2.46, p. 282. Injectivity of the
    source inclusion proves single-valuedness; the target
    map need not be injective. *)
Definition riemannian_map_coordinates (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
    partial_function (R_n R m) (R_n R n).
Proof.
refine (@Build_partial_function (R_n R m) (R_n R n)
  (fun z w=>exists x : riemannian_metric_space hg, val x=z /\ val (f x)=w) _).
move=> z w v [x [hx <-]] [y [hy <-]].
have hxy : x=y := val_inj (eq_trans hx (esym hy)).
by rewrite hxy.
Defined.

(** Source for [riemannian_map_coordinates_graph]: exact
    original coordinate values at every chart point,
    supporting 3.2.46, p. 282. *)
Lemma riemannian_map_coordinates_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h) f x y :
  partial_function_graph (@riemannian_map_coordinates R m n A B g h hg hh f) (val x) y <->
    val (f x)=y.
Proof.
split; last by move=> hEq; exists x; split.
move=> [z [hz hEq]]; have hzx : z=x := val_inj hz; by rewrite -hzx.
Qed.

(** Source for [riemannian_map_coordinates_domain]: the
    coordinate graph has precisely the original source A,
    supporting 3.2.46, p. 282. Empty and disconnected
    charts keep their actual domain; no outside value is assigned. *)
Lemma riemannian_map_coordinates_domain (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h) f z :
  partial_function_domain (@riemannian_map_coordinates R m n A B g h hg hh f) z <-> A z.
Proof.
split.
- move=> [w [x [<- _]]]; exact: set_valP x.
- move=> hz.
  pose x : riemannian_metric_space hg :=
    @exist [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
      (fun y=>y \in (A : set (inner_metric_space (@euclidean_inner_productP R m)))) z (mem_set hz).
  exists (val (f x)); exists x; by split.
Qed.

(** Source for [riemannian_coordinate_representative_exists]:
    an auxiliary total representative agrees with the entire
    actual coordinate graph, supporting 3.2.46, p. 282.
    Existence uses only the earlier sealed function extension;
    outside values remain irrelevant to the public partial graph. *)
Lemma riemannian_coordinate_representative_exists (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  exists F : R_n R m -> R_n R n, forall x : riemannian_metric_space hg, F (val x)=val (f x).
Proof.
pose P := @riemannian_map_coordinates R m n A B g h hg hh f.
pose F := @PartialFunctionExtension.value (R_n R m) (R_n R n) P 0.
have hF := @PartialFunctionExtension.laws (R_n R m) (R_n R n) P 0.
exists F=> x; apply: hF.
apply: (@riemannian_map_coordinates_graph R m n A B g h hg hh f x (val (f x))).2; by [].
Qed.
