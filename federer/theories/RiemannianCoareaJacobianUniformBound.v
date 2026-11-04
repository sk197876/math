(** Federer (1969), 3.2.46, p. 282: the
    actual target-degree Jacobian has a global finite
    bound for an original Lipschitz map. This discharges
    the signed-integrability obligation in the extension
    of 3.2.12, pp. 249–250. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianPathLipschitz
  RiemannianMapJacobian RiemannianDifferentialFiniteBound RiemannianLinearJacobianUpperBound
  PartialFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_jacobian_uniform_bound]:
    a proved uniform finite bound for the actual
    partial J_n f, supporting the signed approximation
    in 3.2.46, p. 282. The constant is
    auxiliary and need not be sharp. No bounded-
    Jacobian, derivative-field or rank premise is added
    to the original path-Lipschitz assumption. *)
Theorem riemannian_coarea_jacobian_uniform_bound (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f -> exists C : R, 0<C /\
    forall x j, partial_function_graph (extended_riemannian_map_jacobian f n) x j -> (j<=C%:E)%E.
Proof.
move=> hLip.
have [K [hK hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
have hFourK : 0<4*K by rewrite mulr_gt0 // ltr0n.
exists ((4*K)^+n); split; first exact (exprn_gt0 n hFourK).
move=> x j [r [[D [hD hValue]] hEmbed]].
rewrite -hEmbed -hValue lee_fin.
exact (@riemannian_target_linear_jacobian_bound R m n (g (val x)) (h (val (f x)))
  (riemannian_tensor_inner hg (set_valP x)) (riemannian_tensor_inner hh (set_valP (f x)))
  D (4*K) (ltW hFourK)
  (@riemannian_differential_finite_bound R m n A B g h hg hh f K hK hBound x D hD)).
Qed.
