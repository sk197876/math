(** Federer (1969), 2.2.10, p. 67: the two shrinking closed branches have
    limit points u,v. Disjointness of their images gives distinct f(u),f(v);
    Hausdorff neighborhoods and continuity eventually separate the entire
    branch images. The lemma isolates that consequence of the branch laws,
    independently of the recursive branch choices. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP ClosedShrinkingIntersection BorelSeparation
  BorelSeparationRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [shrinking_closed_images_eventually_separated]: supporting
    contradiction step for Federer 2.2.10(1), p. 67. Two nested nonempty
    closed sequences with vanishing diameters and disjoint initial images
    eventually have Borel-separated images under a continuous map to a
    Hausdorff space. *)
Lemma shrinking_closed_images_eventually_separated (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : nat -> set T) :
  is_complete_metric_space T -> hausdorff_space Y -> continuous f ->
  (forall n, C n !=set0) -> (forall n, D n !=set0) ->
  (forall n, closed (C n)) -> (forall n, closed (D n)) ->
  (forall n m, (n <= m)%N -> C m `<=` C n) ->
  (forall n m, (n <= m)%N -> D m `<=` D n) ->
  (forall e : R, 0 < e -> exists n, forall x y, C n x -> C n y -> mdist x y < e) ->
  (forall e : R, 0 < e -> exists n, forall x y, D n x -> D n y -> mdist x y < e) ->
  (f @` C 0%N) `&` (f @` D 0%N) = set0 ->
  exists n, borel_separated (f @` C n) (f @` D n).
Proof.
move=> hT hY hf hc hd hcc hdc hcn hdn hcs hds hdis.
have [u hu] := closed_shrinking_metric_intersection hT hc hcc hcn hcs.
have [v hv] := closed_shrinking_metric_intersection hT hd hdc hdn hds.
have hneq : f u != f v.
  apply/negP=> /eqP he.
  have hh : ((f @` C 0%N) `&` (f @` D 0%N)) (f u).
    split; [by exists u|exists v=> //; exact: esym he].
  by rewrite hdis in hh.
rewrite open_hausdorff in hY.
have [[U V] [huU hvV] [hU hV /eqP hUV]] := hY (f u) (f v) hneq.
have huU' : U (f u) by move: huU; rewrite inE.
have hvV' : V (f v) by move: hvV; rewrite inE.
have hnU : nbhs u (f @^-1` U).
  apply: hf; have ho := hU; rewrite openE in ho; exact: ho _ huU'.
have hnV : nbhs v (f @^-1` V).
  apply: hf; have ho := hV; rewrite openE in ho; exact: ho _ hvV'.
have [e he heU] := proj1 (metricType_numDomainType.nbhs_mdistP u _) hnU.
have [r hr hrV] := proj1 (metricType_numDomainType.nbhs_mdistP v _) hnV.
have [i hi] := hcs e he; have [j hj] := hds r hr.
exists (maxn i j); apply: (@disjoint_open_borel_separators Y _ _ U V hU hV hUV).
- move=> y [x hx <-]; apply: heU; apply: hi; first exact: hu.
  exact: hcn i (maxn i j) (leq_maxl _ _) x hx.
- move=> y [x hx <-]; apply: hrV; apply: hj; first exact: hv.
  exact: hdn j (maxn i j) (leq_maxr _ _) x hx.
Qed.
