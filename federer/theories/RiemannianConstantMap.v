(** Federer (1969), 3.2.46, p. 282: constant maps satisfy the
    original path-distance Lipschitz hypothesis. This supporting fact
    tests singular maps and zero-dimensional targets without assuming
    any Jacobian or fibre formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianPathLipschitz RiemannianDistance RiemannianDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_constant_map_lipschitz]: the actual
    original-rho Lipschitz condition in Federer 3.2.46, p. 282,
    for a constant map, including disconnected source charts. *)
Lemma riemannian_constant_map_lipschitz (R:realType) m n A B g h
    (hg:@is_continuous_riemannian_tensor R m A g)
    (hh:@is_continuous_riemannian_tensor R n B h)
    (b:riemannian_metric_space hh):
  is_riemannian_path_lipschitz (fun _:riemannian_metric_space hg=>b).
Proof.
exists 1; split; first exact:ltr01.
move=>x y.
rewrite (@riemannian_distance_self R n B h hh (val b) (set_valP b)) mul1e.
exact:riemannian_distance_nonnegative.
Qed.
