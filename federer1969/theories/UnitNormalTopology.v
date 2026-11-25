(** Normal-coordinate topology supporting Federer (1969), 2.10.30, p. 195.
    Continuity is derived from the project's inner-product norm topology,
    and compact scalar sections are continuous images of closed slices.
    These supporting facts underlie compactness and the boundary-sphere
    assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  OrthonormalFamilies InnerCoordinateContinuity RealMetricBackground
  UnitNormalGeometry SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Topology.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation E := (inner_metric_space hB).
Variable u : V.
Local Notation c := (inner_coordinate hB u).

(** Source for [normal_foot_continuous]: supporting
    continuous orthogonal projection for the compact-set
    assertions of 2.10.30, p. 195. *)
Lemma normal_foot_continuous : continuous (normal_foot hB u : E -> E).
Proof.
move=> x; apply: continuousB; first exact: cvg_id.
apply: continuousZ; [exact: inner_coordinate_continuous|exact: cst_continuous].
Qed.

(** Source for [normal_line_continuous]: supporting continuous normal-line
    parametrisation in 2.10.30, p. 195 *)
Lemma normal_line_continuous (y : E) :
  continuous (fun t : real_line_metric R => (y+t*:u : E)).
Proof.
move=> t; apply: continuousD; first exact: cst_continuous.
apply: continuousZ; [exact: cvg_id|exact: cst_continuous].
Qed.

(** Source for [normal_scalar_section_compact]: supporting
    compact scalar sections of a compact S in
    2.10.30, p. 195. Empty sections are included;
    no endpoints are chosen by this argument. *)
Theorem normal_scalar_section_compact (S : set E) (y : V) :
  B u u= 1 -> inner_coordinate hB u y=0 -> compact S ->
  compact (normal_scalar_section u S y).
Proof.
move=> hu hy hS.
pose C : set E := S `&` ((normal_foot hB u : E -> E) @^-1` [set y]).
have hfoot : closed ((normal_foot hB u : E -> E) @^-1` [set y]).
  apply: (@preimage_closed E E (normal_foot hB u) [set y]).
  - move=> x _; exact: normal_foot_continuous.
  - exact (@accessible_closed_set1 E (hausdorff_accessible (@metric_hausdorff R E)) y).
have hC : compact C.
  apply: (subclosed_compact (closedI
    (compact_closed (@metric_hausdorff R E) hS) hfoot) hS).
  by move=> x [hx _].
have him : c @` C=normal_scalar_section u S y.
  apply/seteqP; split=> t.
  - move=> [x [hx hxy] <-].
    have hfootxy : normal_foot hB u x=y by exact hxy.
    have he := normal_decomposition hB u x.
    by rewrite /normal_scalar_section /= -hfootxy he.
  - move=> ht; exists (y+t*:u).
    + split=> //; exact (@normal_line_foot R V B hB u hu y t hy).
    + exact (@normal_line_coordinate R V B hB u hu y t hy).
rewrite -him; apply: continuous_compact _ hC.
exact: continuous_subspaceT (@inner_coordinate_continuous R V B hB u).
Qed.
End Topology.
