(** Federer (1969), 3.2.46, p. 282: the actual constant-map
    differential and zeroth Jacobian. These concrete consequences
    test singular maps and positive degree-zero fibre measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialLinear
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMapDifferentialUP
  RiemannianMapDifferential RiemannianMapJacobian RiemannianLinearJacobian
  PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_constant_differential]: actual derivative
    zero for a constant map in Federer 3.2.46, p. 282,
    by 3.1.1, pp. 209–210. No differential field is assumed. *)
Lemma riemannian_constant_differential (R:realType) m n A B g h
    (hg:@is_continuous_riemannian_tensor R m A g)
    (hh:@is_continuous_riemannian_tensor R n B h)
    (b:riemannian_metric_space hh) (x:riemannian_metric_space hg):
  partial_function_graph (riemannian_map_differential (fun _:riemannian_metric_space hg=>b)) x 0.
Proof.
apply/riemannian_map_differential_graph.
exists (fun _:R_n R m=>val b); split; first by move=>y.
apply:(norm_differential_constant
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
exact (@riemannian_tensor_domain_open R m A g hg (val x) (set_valP x)).
Qed.

(** Source for [riemannian_constant_zeroth_jacobian]: J_0= 1
    for the actual singular constant map in 3.2.46, p. 282.
    This is an equality of actual partial graphs, not an
    everywhere extension of a possibly missing derivative. *)
Lemma riemannian_constant_zeroth_jacobian (R:realType) m n A B g h
    (hg:@is_continuous_riemannian_tensor R m A g)
    (hh:@is_continuous_riemannian_tensor R n B h)
    (b:riemannian_metric_space hh) (x:riemannian_metric_space hg) z:
  partial_function_graph (extended_riemannian_map_jacobian
    (fun _:riemannian_metric_space hg=>b) 0) x z <-> z=(1:R)%:E.
Proof.
have hD:=riemannian_constant_differential b x.
have hJ:partial_function_graph (riemannian_map_jacobian
    (fun _:riemannian_metric_space hg=>b) 0) x 1.
  exists 0; split; first exact hD.
  exact (@riemannian_linear_jacobian_zero_degree R m n
    (g (val x)) (h (val b)) (riemannian_tensor_inner hg (set_valP x))
    (riemannian_tensor_inner hh (set_valP b)) (0:Hom (R_n R m) (R_n R n))).
split.
- move=>[r [hr hEq]].
  have hr1:r= 1:=partial_function_single_valued hr hJ.
  by rewrite -hEq hr1.
- move=>->; exists 1; by split.
Qed.
