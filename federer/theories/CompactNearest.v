(** Federer (1969), 1.8.1, p. 38: supporting separation of a point from the
    compact convex hull. The nearest-point method is the one developed in
    1.7.13, p. 37; compactness gives existence without a separate
    completeness hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerNearestUP CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_inner_nearest_exists]: Federer 1.8.1,
    p. 38, supporting compact-set nearest point used for local convex
    separation; compare 1.7.13, p. 37. Convexity is not required for
    existence, and no finite-dimensional hypothesis is imposed. *)
Theorem compact_inner_nearest_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V)
    (C : set (inner_metric_space hB)) : C !=set0 -> compact C ->
    exists c, is_inner_nearest hB a C c.
Proof.
move=> hn hC.
pose M := inner_metric_space hB.
have hf : continuous (fun x : M => (-inner_norm hB (a-x) : R^o)).
  move=> x; apply: continuousN.
  apply: (@continuous_comp (Topological.clone M _) (Topological.clone M _)
    (Topological.clone R^o _) (fun y => a-y) Num.norm x).
  - apply: continuousB; first exact: cst_continuous.
    by [].
  - exact: norm_continuous.
have [c [hc hmax]] := @continuous_compact_maximum R (Topological.clone M _) C
  (fun x => -inner_norm hB (a-x)) hn hC hf.
exists c; constructor=> // y hy.
have hh := hmax y hy; by rewrite lerN2 in hh.
Qed.
