(** Federer (1969), 1.7.3, p. 29: the compact constraint set C_j in the
    principal-axis argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerBoundedness InnerFiniteCompactness
  OrthonormalFamilies LinearBasis.
From Federer Require Import InnerCoordinateContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Constraint.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable k : nat.
Variable e : 'I_k -> V.

(** Source for [constrained_unit_sphere]: Federer 1.7.3,
    p. 29, the displayed set C_j: unit vectors orthogonal to all
    previously selected vectors. The family is indexed from zero. *)
Definition constrained_unit_sphere : set M :=
  [set x | inner_norm hB x = 1 /\ forall i, B x (e i) = 0].

(** Source for [inner_unit_sphere_closed]: Federer 1.7.3,
    p. 29, supporting closedness of the unit sphere under the norm metric. *)
Lemma inner_unit_sphere_closed : closed [set x : M | inner_norm hB x = 1].
Proof.
change (closed ((fun x : M => (`|x| : R^o)) @^-1` [set 1])).
apply: preimage_closed; first by move=> x _; exact: norm_continuous.
apply: compact_closed; [exact: norm_hausdorff | exact: compact_set1].
Qed.

(** Source for [inner_orthogonal_hyperplane_closed]: Federer
    1.7.3, p. 29, supporting closedness of a constraint x.e_i=0. *)
Lemma inner_orthogonal_hyperplane_closed v : closed [set x : M | B x v = 0].
Proof.
have hE : [set x : M | B x v = 0] = [set x : M | inner_coordinate hB v x = 0].
  apply: funext => x.
  change ((B x v = 0) = (inner_coordinate hB v x = 0)).
  by rewrite inner_coordinateE.
rewrite hE.
change (closed ((fun x : M => inner_coordinate hB v x) @^-1` [set 0])).
apply: preimage_closed; first by move=> x _; exact: inner_coordinate_continuous.
apply: compact_closed; [exact: norm_hausdorff | exact: compact_set1].
Qed.

(** Source for [constrained_unit_sphere_closed]: Federer 1.7.3,
    p. 29, C_j is the intersection of the closed unit sphere and
    closed orthogonality constraints. *)
Lemma constrained_unit_sphere_closed : closed constrained_unit_sphere.
Proof.
have hE : constrained_unit_sphere =
  [set x : M | inner_norm hB x = 1] `&`
  \bigcap_i [set x : M | B x (e i) = 0].
  apply/seteqP; split=> x [hx ho]; split=> //.
  - by move=> i _; exact: ho.
  - move=> i; exact: ho i I.
rewrite hE; apply: closedI; first exact: inner_unit_sphere_closed.
apply: closed_bigI => i _; exact: inner_orthogonal_hyperplane_closed.
Qed.

(** Source for [constrained_unit_sphere_compact]: Federer 1.7.3,
    p. 29, the constraint set is compact in finite dimension, by
    the bounded-compactness criterion already proved in 1.7.1. *)
Theorem constrained_unit_sphere_compact n (b : 'I_n -> V) :
  is_basis b -> compact constrained_unit_sphere.
Proof.
move=> hb; apply: (@inner_finite_basis_boundedly_compact R V B hB n b hb).
- exact: constrained_unit_sphere_closed.
- exists 1 => x [hx _]; by rewrite hx.
Qed.
End Constraint.
