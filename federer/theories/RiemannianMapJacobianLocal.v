(** Federer (1969), 3.2.46, p. 282: local
    coordinate representatives compute the same actual
    Jacobian. Membership proofs and extension values outside
    the open patch do not change that value or domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerProductUP RiemannianTensorUP RiemannianMetricCarrier
  RiemannianLinearJacobian RiemannianJacobianProofIndependence
  RiemannianMapDifferential RiemannianMapDifferentialLocal RiemannianMapJacobian
  RiemannianTargetJacobian PartialFunctionUP PartialFunctionPrecomposition
  MeasureStepIntegralIdentification ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_tensor_jacobian_target_equal]:
    the actual target metric depends on the original point,
    not its membership proof, supporting 3.2.46, p. 282.
    Equality follows from the independent exterior norm laws,
    without an additional proof-irrelevance assumption. *)
Lemma riemannian_tensor_jacobian_target_equal (R : realType) m n B h
    (hh : @is_continuous_riemannian_tensor R n B h) C
    (hC : @is_inner_product R (R_n R m) C) k (D : Hom (R_n R m) (R_n R n))
    z w (hz : B z) (hw : B w) : z=w ->
  riemannian_linear_jacobian hC (riemannian_tensor_inner hh hz) k D=
    riemannian_linear_jacobian hC (riemannian_tensor_inner hh hw) k D.
Proof.
move=> hEq; move: hw; rewrite -hEq=> hw.
exact: riemannian_linear_jacobian_inner_proof_independent.
Qed.

(** Source for [riemannian_map_jacobian_local_coordinates]:
    exact agreement of the original Euclidean-source Jacobian
    with any actual local coordinate extension, supporting
    3.2.46, p. 282. Neither differentiability nor a
    globally chosen extension is a premise. All ranks and
    degrees, including zero, keep their actual domains. *)
Theorem riemannian_map_jacobian_local_coordinates (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (F : R_n R m -> R_n R n) (hF : forall z, B (F z)) :
  open U -> U `<=` A ->
  (forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x)) ->
  forall a : riemannian_metric_space hg, U (val a) -> forall k j,
    (partial_function_graph (riemannian_map_euclidean_source_jacobian f k) a j <->
      partial_function_graph (@target_riemannian_jacobian R m n B h hh F hF k) (val a) j).
Proof.
move=> hU hUA hAgreement a ha k j.
have hDiff := @riemannian_map_differential_local_coordinates R m n A B g h hg hh f U F
  hU hUA hAgreement a ha.
have hValue D : riemannian_linear_jacobian (@euclidean_inner_productP R m)
    (riemannian_tensor_inner hh (set_valP (f a))) k D=
    riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (hF (val a))) k D.
  exact (@riemannian_tensor_jacobian_target_equal R m n B h hh
    (@euclidean_inner_product R m) (@euclidean_inner_productP R m) k D
    (val (f a)) (F (val a)) (set_valP (f a)) (hF (val a)) (esym (hAgreement a ha))).
split.
- move=> [D [hD hJ]].
  apply: (@target_riemannian_jacobian_graph R m n B h hh F hF k (val a) j).2.
  exists D; split; first exact: (hDiff D).1 hD.
  exact (eq_trans (esym (hValue D)) hJ).
- move=> /(@target_riemannian_jacobian_graph R m n B h hh F hF k (val a) j) [D [hD hJ]].
  exists D; split; first exact: (hDiff D).2 hD.
  exact (eq_trans (hValue D) hJ).
Qed.

(** Source for [riemannian_map_extended_jacobian_local_coordinates]:
    the same exact local agreement for the extended-real
    integrands of 3.2.46, p. 282. This retains the
    original partial graph rather than an almost-everywhere
    selected derivative or an assigned outside value. *)
Corollary riemannian_map_extended_jacobian_local_coordinates (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (F : R_n R m -> R_n R n) (hF : forall z, B (F z)) :
  open U -> U `<=` A ->
  (forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x)) ->
  forall a : riemannian_metric_space hg, U (val a) -> forall k z,
    (partial_function_graph
      (partial_real_function_embed (riemannian_map_euclidean_source_jacobian f k)) a z <->
    partial_function_graph (@extended_target_riemannian_jacobian R m n B h hh F hF k) (val a) z).
Proof.
move=> hU hUA hAgreement a ha k z.
have hReal := @riemannian_map_jacobian_local_coordinates R m n A B g h hg hh f U F hF
  hU hUA hAgreement a ha k.
split.
- move=> [r [hr hrz]]; exists r; split; last exact hrz.
  exact: (hReal r).1 hr.
- move=> [r [hr hrz]]; exists r; split; last exact hrz.
  exact: (hReal r).2 hr.
Qed.
