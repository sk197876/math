(** Federer (1969), 2.10.29, p. 195, used in 3.2.24,
    p. 260: finite Euclidean powers of a scalar Borel set
    are Borel. Coordinate membership, continuity and finite
    intersection suffice; no new product topology is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanSetPowers EuclideanCoordinateTopology
  TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_set_power_borel]: supporting Borel
    property of the Cantor powers of 2.10.29, p. 195,
    supplying the Borel counterexample in 3.2.24, p. 260.
    Every finite power is allowed, including the empty power. *)
Lemma euclidean_set_power_borel (R:realType) q (A:set (real_line_metric R)):
  borel_set A ->@borel_set (inner_metric_space (@euclidean_inner_productP R q))
    (euclidean_set_power q A).
Proof.
move=>hA; case:q=>[|q].
- have hWhole:euclidean_set_power 0 A=setT.
    apply/seteqP; split=>x _; first exact Logic.I.
    move=>i; by move:(ltn_ord i); rewrite ltn0.
  rewrite hWhole; exact:open_borel_set openT.
- have hSet:euclidean_set_power q.+1 A=
      (\bigcap_(i in @setT 'I_q.+1) ((fun x:inner_metric_space (@euclidean_inner_productP R q.+1)=>x i) @^-1` A)).
    by apply/seteqP; split=>x hx; [move=>i _; exact:hx|move=>i; exact:(hx i Logic.I)].
  rewrite hSet; apply:borel_set_countable_intersection (countableP setT) _ _.
  + by exists ord0.
  + move=>i _; exact:(continuous_borel_preimage (@euclidean_coordinate_continuous R q.+1 i) hA).
Qed.
