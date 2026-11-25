(** Private Borel range reduction supporting Federer (1969), 2.3.6, p. 77.
    Source context and scope: ClosedSubsetBorelRetractionUP.v. Off the
    closed set the map takes one fixed value in it. Only general subtype
    topology is used. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology subtype_topology.
From Federer Require Import MetricSubsetBackground BorelFunctionUP TopologicalBorel
  BorelFamilyBasic ClosedSubsetBorelRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_subset_borel_retraction_exists]: supporting
    existence for the separable-support reduction in Federer 2.3.6,
    p. 77. Empty support is handled separately in the measure argument. *)
Lemma closed_subset_borel_retraction_exists (R : realType) (Y : metricType R)
    (S : set Y) (s0 : metric_subset S) : closed S ->
  exists r : Y -> metric_subset S, is_closed_subset_borel_retraction r.
Proof.
move=> hS.
pose r y : metric_subset S := if pselect (S y) is left hy then Sub y (mem_set hy) else s0.
have hr y : S y -> val (r y) = y.
  move=> hy; rewrite /r; case: (pselect (S y))=> hs //; exfalso; exact: hs hy.
exists r; split=> // U hU.
rewrite /open /= in hU.
have [V hV he] := hU.
have heq : r @^-1` U = (S `&` V) `|` (if pselect (U s0) then ~` S else set0).
  apply/seteqP; split=> y.
  - move=> hu; case: (pselect (S y))=> hs.
    + left; split=> //; rewrite -he in hu; change (V (val (r y))) in hu.
      by rewrite (hr y hs) in hu.
    + right; have hru : U s0.
        move: hu; rewrite /preimage /r /=; case: (pselect (S y))=> hy.
        * exfalso; exact: hs hy.
        * by [].
      case: (pselect (U s0))=> hu0 //; exfalso; exact: hu0 hru.
  - move=> [[hs hv]|hu].
    + rewrite /preimage -he; change (V (val (r y))).
      by rewrite (hr y hs).
    + move: hu; case: (pselect (U s0))=> hu0; last by move=> [].
      move=> hs; rewrite /preimage /r /=; case: (pselect (S y))=> hy.
      * exfalso; exact: hs hy.
      * exact hu0.
rewrite heq; apply: (borel_family_binary_union (borel_sets_family Y)).
- exact: (borel_family_binary_intersection (borel_sets_family Y)
    (closed_borel_set hS) (open_borel_set hV)).
- case: (pselect (U s0))=> hcase; first exact: borel_set_complement (closed_borel_set hS).
  exact: open_borel_set open0.
Qed.
