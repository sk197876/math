(** Federer (1969), 2.10.21, p. 182: convergence in the cartesian product
    means convergence at every point. Connect the explicit metric eventual
    inequalities to the actual product topology before applying the
    compact-uniform theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import LipschitzUP LipschitzCompactConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_functions_product_convergence]: direct
    pointwise meaning of product convergence in
    2.10.21, p. 182, for arbitrary filters. *)
Lemma metric_functions_product_convergence (R : realType) (I : Type) (X Y : metricType R)
    (F : set_system I) (FF : Filter F)
    (u : I -> prod_topology (fun _ : X => Y)) (f : prod_topology (fun _ : X => Y)) :
  (u @ F --> f) <-> metric_functions_pointwise_converge F u f.
Proof.
have FU : Filter (u @ F) := @fmap_filter I (prod_topology (fun _ : X => Y)) u F FF.
have he := @pointwise_cvgP X Y (u @ F) f FU.
split.
- move=> hu x e heps.
  have hx := (proj1 he hu) x.
  exact: (proj1 (metricType_numDomainType.cvgrPdist_lt _ _) hx e heps).
- move=> hp; apply: (proj2 he)=> x.
  apply: (proj2 (metricType_numDomainType.cvgrPdist_lt _ _))=> e heps.
  exact: hp x e heps.
Qed.

(** Source for [lipschitz_product_compact_uniform]: direct
    convergence equivalence of 2.10.21, p. 182,
    now stated with the actual cartesian product
    topology and uniform convergence on every compact set. *)
Theorem lipschitz_product_compact_uniform (R : realType) (I : Type) (X Y : metricType R)
    (F : set_system I) (FF : Filter F)
    (u : I -> prod_topology (fun _ : X => Y)) (f : prod_topology (fun _ : X => Y)) (s : R) :
  is_metric_lipschitz_bound setT f s ->
  (forall i, is_metric_lipschitz_bound setT (u i) s) ->
  ((u @ F --> f) <-> metric_functions_compact_uniformly_converge F u f).
Proof.
move=> hf hu.
exact: (iff_trans (@metric_functions_product_convergence R I X Y F FF u f)
  (@lipschitz_pointwise_compact_uniform R I X Y F FF u f s hf hu)).
Qed.
