(** Federer (1969), 3.2.46, p. 282: the actual
    Riemannian Jacobian of the original map, computed with
    its sealed coordinate differential and the original
    source and target forms. Local extensions and frames
    are absent from its public specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  RiemannianTensorUP RiemannianMetricCarrier RiemannianLinearJacobian
  RiemannianJacobianVolumeFactor RiemannianChartVolumeDensity
  RiemannianMapDifferentialUP RiemannianMapDifferential
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourcePostcomposition
  PartialDensityProduct MeasureStepIntegralIdentification ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Jacobian.
Context (R : realType) m n A B g h
  (hg : @is_continuous_riemannian_tensor R m A g)
  (hh : @is_continuous_riemannian_tensor R n B h)
  (f : riemannian_metric_space hg -> riemannian_metric_space hh).
Local Notation X := (riemannian_metric_space hg).

(** Source for [has_riemannian_map_jacobian]: independent
    value law for the actual kth exterior norm of Df(a),
    with the two actual metric forms, supporting 3.2.46,
    p. 282. No transformation identity is among the laws. *)
Definition has_riemannian_map_jacobian k (a : X) j :=
  exists D, has_riemannian_map_differential f a D /\
    riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP a))
      (riemannian_tensor_inner hh (set_valP (f a))) k D=j.

(** Source for [riemannian_map_jacobian]: the actual
    Riemannian Jacobian in 3.2.46, p. 282. This is
    ordinary postcomposition of the already sealed actual
    differential and exterior norm, with no chosen field. *)
Definition riemannian_map_jacobian k : partial_function X R :=
  partial_function_source_postcompose (riemannian_map_differential f)
    (fun a D=>riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP a))
      (riemannian_tensor_inner hh (set_valP (f a))) k D).

(** Source for [riemannian_map_jacobian_graph]: exact
    original-map graph law for 3.2.46, p. 282. *)
Lemma riemannian_map_jacobian_graph k a j :
  partial_function_graph (riemannian_map_jacobian k) a j <->
    has_riemannian_map_jacobian k a j.
Proof.
split.
- move=> [D [hD hJ]]; exists D; split; last exact hJ.
  exact: (riemannian_map_differential_graph f a D).1 hD.
- move=> [D [hD hJ]]; exists D; split; last exact hJ.
  exact: (riemannian_map_differential_graph f a D).2 hD.
Qed.

(** Source for [riemannian_map_jacobian_nonnegative]:
    nonnegativity of the actual exterior norm in 3.2.46,
    p. 282, including zero-degree and singular maps. *)
Lemma riemannian_map_jacobian_nonnegative k a j :
  partial_function_graph (riemannian_map_jacobian k) a j -> 0<=j.
Proof.
move=> /(riemannian_map_jacobian_graph k a j) [D [_ <-]].
exact: riemannian_linear_jacobian_nonnegative.
Qed.

(** Source for [extended_riemannian_map_jacobian]: the same
    actual finite Jacobian as an extended-real partial
    integrand, supporting 3.2.46, p. 282. Its domain
    remains exactly the actual differentiability locus. *)
Definition extended_riemannian_map_jacobian k :=
  partial_real_function_embed (riemannian_map_jacobian k).

(** Source for [riemannian_map_euclidean_source_jacobian]:
    the same original Df with Euclidean source and actual
    target metric, supporting source-density cancellation in
    3.2.46, p. 282. This is an intermediate coordinate
    Jacobian, not a replacement of the public metric. *)
Definition riemannian_map_euclidean_source_jacobian k : partial_function X R :=
  partial_function_source_postcompose (riemannian_map_differential f)
    (fun a D=>riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (set_valP (f a))) k D).

(** Source for [riemannian_map_source_volume_graph]: exact
    cancellation of sqrt(discr g) with the source part
    of the actual area Jacobian, supporting 3.2.46,
    p. 282. The partial domain is unchanged, and
    singular maps and dimension zero are retained. *)
Theorem riemannian_map_source_volume_graph a j :
  partial_function_graph (riemannian_map_euclidean_source_jacobian m) a j <->
    exists q, partial_function_graph (riemannian_map_jacobian m) a q /\
      q*riemannian_chart_volume_density hg a=j.
Proof.
split.
- move=> [D [hD <-]].
  exists (riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP a))
    (riemannian_tensor_inner hh (set_valP (f a))) m D).
  split; first by exists D; split.
  exact: riemannian_area_jacobian_volume_factor.
- move=> [q [[D [hD <-]] <-]]; exists D; split; first exact hD.
  exact (esym (@riemannian_area_jacobian_volume_factor R m n (g (val a)) (h (val (f a)))
    (riemannian_tensor_inner hg (set_valP a))
    (riemannian_tensor_inner hh (set_valP (f a))) D)).
Qed.

(** Source for [riemannian_map_extended_source_volume_graph]:
    the same cancellation as an exact density-product
    graph identity for the integral of 3.2.46, p. 282.
    The total density supplies no values where the original
    Jacobian is undefined. *)
Theorem riemannian_map_extended_source_volume_graph a z :
  partial_function_graph
    (partial_real_function_embed (riemannian_map_euclidean_source_jacobian m)) a z <->
  partial_function_graph (partial_density_product (extended_riemannian_map_jacobian m)
    (partial_function_total (fun x : X=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)))) a z.
Proof.
split.
- move=> [j [/(riemannian_map_source_volume_graph a j) [q [hq <-]] <-]].
  apply/partial_density_product_graph.
  exists q%:E,(riemannian_chart_volume_density hg a)%:E; split.
  + exists q; by split.
  + split; first by [].
    by rewrite -EFinM.
- move=> /partial_density_product_graph [q [d [[r [hr <-]] [hd <-]]]].
  change ((riemannian_chart_volume_density hg a)%:E=d) in hd.
  rewrite -hd -EFinM.
  exists (r*riemannian_chart_volume_density hg a); split; last by [].
  apply: (riemannian_map_source_volume_graph a _).2.
  exists r; by split.
Qed.
End Jacobian.
