(** Federer (1969), 2.9.19, p. 165: choose a finite variation partition of
    arbitrarily small mesh and with length sum arbitrarily close to the
    total variation. Specifications precede the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [variation_partition_mesh_lt]: direct mesh condition
    t_(j+1)-t_j<d in Federer 2.9.19, p. 165 The existing partition
    convention permits repeated terms. *)
Fixpoint variation_partition_mesh_lt (R : realType) (d : R) (s : seq R) : bool :=
  match s with
  | a :: ((b :: _) as rest) => (b-a<d) && variation_partition_mesh_lt d rest
  | _ => true
  end.

(** Source for [is_fine_near_maximal_variation_partition]: direct partition
    laws used in Federer 2.9.19, p. 165 The partition joins a to b, has mesh
    below d, and its metric length sum is within e of the finite real total
    variation. It specifies the required laws without choosing any
    particular subdivision. *)
Definition is_fine_near_maximal_variation_partition (R : realType) (Y : metricType R)
    (g : R -> Y) (a b d e : R) (s : seq R) :=
  is_variation_partition a b s /\ variation_partition_mesh_lt d s /\
    fine (curve_variation g a b)-chain_sum g s<e.

(** Source for [chain_sum_ge_endpoint_distance]: supporting
    refinement inequality for the partition choice in
    Federer 2.9.19, p. 165, from the
    triangle inequality in 2.5.16, p. 109.
    Every finite metric chain has length at least
    the distance between its endpoints. Empty and
    singleton chains have coincident endpoints and zero length. *)
Lemma chain_sum_ge_endpoint_distance (R : realType) (Y : metricType R)
    (g : R -> Y) (s : seq R) (a : R) :
  mdist (g (head a s)) (g (last a s))<=chain_sum g s.
Proof.
elim: s=> [|t [|u rest] ih] /=; first by rewrite mdistxx.
- by rewrite mdistxx.
- exact: le_trans (metric_triangle (g t) (g u) (g (last u rest))) (lerD (lexx _) ih).
Qed.
