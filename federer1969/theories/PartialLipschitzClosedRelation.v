(** Federer (1969), 3.2.14, p. 252: closure preserves
    rectifiability. The distance inequality of a Lipschitz
    graph survives topological closure, even in incomplete
    metric spaces. These are proved laws, not added axioms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology num_normedtype
  pseudometric_normed_Zmodule normed_module.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz MetricPairDistance
  TopologicalProductMaps RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory
  numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_pair_constraint_closed]:
    supporting closed distance comparison for Federer 3.2.14,
    p. 252. The first graph point is fixed and the second
    varies in the product topology. *)
Lemma metric_lipschitz_pair_constraint_closed (R : realType)
    (X Y : metricType R) (L : R) (p : X * Y) :
  closed [set q : X * Y | mdist p.2 q.2 <= L * mdist p.1 q.1].
Proof.
pose u : X * Y -> R^o := fun q => mdist p.2 q.2.
pose v : X * Y -> R^o := fun q => L * mdist p.1 q.1.
have hpairY : continuous (fun q : X * Y => (p.2,q.2)).
  apply: topological_pair_continuous; first exact: cst_continuous.
  exact: second_projection_continuous.
have hpairX : continuous (fun q : X * Y => (p.1,q.1)).
  apply: topological_pair_continuous; first exact: cst_continuous.
  exact: first_projection_continuous.
have hu : continuous u.
  move=> q; exact: continuous_comp (hpairY q)
    (@metric_pair_distance_continuous R Y (p.2,q.2)).
have hw : continuous (fun q : X * Y => (mdist p.1 q.1 : R^o)).
  move=> q; exact: continuous_comp (hpairX q)
    (@metric_pair_distance_continuous R X (p.1,q.1)).
have hv : continuous v.
  move=> q.
  have hc : {for q, continuous (fun _ : X * Y => (L : R^o))} by exact: cvg_cst.
  exact (@continuousM R [the topologicalType of (X * Y)%type] (fun _ => L)
    (fun q => mdist p.1 q.1) q hc (hw q)).
have hd : continuous (fun q : X * Y => (u q-v q : R^o)).
  move=> q; exact: (@continuousB R R^o [the topologicalType of (X * Y)%type] u v q (hu q) (hv q)).
have he : [set q : X * Y | mdist p.2 q.2 <= L * mdist p.1 q.1]=
    (fun q : X * Y => (u q-v q : R^o)) @^-1` [set t | t <= 0].
  by apply/seteqP; split=> q hq; move: hq; rewrite /= subr_le0.
rewrite he; apply: preimage_closed; last exact: closed_le.
move=> q hq; exact: hd q.
Qed.

(** Source for [partial_lipschitz_graph_closure_bound]:
    supporting the closure assertion of Federer 3.2.14,
    p. 252. Close each variable of the distance inequality
    separately, retaining exactly the same Lipschitz bound. *)
Theorem partial_lipschitz_graph_closure_bound (R : realType)
    (X Y : metricType R) (f : partial_function X Y) (L : R) :
  is_partial_metric_lipschitz_bound f L ->
  forall p q : X * Y,
    closure [set z : X * Y | partial_function_graph f z.1 z.2] p ->
    closure [set z : X * Y | partial_function_graph f z.1 z.2] q ->
    mdist p.2 q.2 <= L * mdist p.1 q.1.
Proof.
move=> [hL hLip] p q hp hq.
pose G := [set z : X * Y | partial_function_graph f z.1 z.2].
have hbase a : G a -> forall b, closure G b ->
    mdist a.2 b.2 <= L * mdist a.1 b.1.
  move=> ha.
  move=> b hb; apply: (@metric_lipschitz_pair_constraint_closed R X Y L a).
  apply: (@closureS [the topologicalType of (X * Y)%type] G
    [set q : X * Y | mdist a.2 q.2 <= L * mdist a.1 q.1] _ b hb).
  move=> z hz; exact: hLip a.1 z.1 a.2 z.2 ha hz.
have hclosed := @metric_lipschitz_pair_constraint_closed R X Y L q.
have hsub : G `<=` [set a : X * Y | mdist q.2 a.2 <= L * mdist q.1 a.1].
  move=> a ha; change (is_true (mdist q.2 a.2<=L*mdist q.1 a.1)).
  rewrite (metric_sym q.2 a.2) (metric_sym q.1 a.1).
  exact: hbase a ha q hq.
have hh := hclosed p (@closureS [the topologicalType of (X * Y)%type] G _ hsub p hp).
change (is_true (mdist q.2 p.2<=L*mdist q.1 p.1)) in hh.
by rewrite (metric_sym q.2 p.2) (metric_sym q.1 p.1) in hh.
Qed.
