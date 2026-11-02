(** Federer (1969), 2.10.9, p. 175, warning that 2.10.8 does not apply to
    the Hausdorff construction. In positive degree, singleton covers can
    have total cost zero while a finite target has positive gauge. Here the
    degree-one case is explicit on every metric space with two positively
    separated points. This is a supporting counterexample, not a correction
    to the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel BorelFamilyBasic BorelCoverCostUP
  MetricDiameterUP MetricDiameter HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_length_cost_not_borel_cover_cost]:
    supporting witness to the nonapplication statement in
    Federer 2.10.9, p. 175. Two singleton Borel sets
    cover a target of positive diameter but both have zero
    degree-one cost. This concerns the cost, not the resulting
    Hausdorff measure, which does satisfy covering laws. *)
Theorem hausdorff_length_cost_not_borel_cover_cost (R : realType) (X : metricType R)
    (x y : X) : (0<mdist x y)%R ->
  ~ is_borel_cover_cost (@hausdorff_diameter_cost R X 1).
Proof.
move=> hxy hc.
have hb z : borel_set ([set z] : set X).
  apply: closed_borel_set; apply: accessible_closed_set1.
  apply: hausdorff_accessible; exact: metric_hausdorff.
pose A := [set x] `|` [set y].
have hA : borel_set A := @borel_family_binary_union X setT (@borel_set X)
  (borel_sets_family X) [set x] [set y] (hb x) (hb y).
pose S (b : bool) : set X := [set if b then x else y].
have hS b : borel_set (S b) := hb _.
have hcover : A `<=` \bigcup_(b in @setT bool) S b.
  move=> z [->|->]; [exists true|exists false]; by [].
have hc0 b : hausdorff_diameter_cost 1 (S b)=0.
  rewrite hausdorff_diameter_cost_one_degree.
  apply/eqP; rewrite eq_le (metric_diameter_nonnegative (extended_metric_diameter_specification (S b))) andbT.
  apply: (metric_diameter_least (extended_metric_diameter_specification (S b)))=> //.
  by move=> u v -> ->; rewrite mdistxx.
have hbound := @borel_cover_cost_cover R X (@hausdorff_diameter_cost R X 1) hc
  [the choiceType of (bool : Type)] setT S A (countableP _) hA (fun b _ => hS b) hcover.
have hz : nonnegative_sum setT (fun b => hausdorff_diameter_cost 1 (S b))=0.
  apply: nonnegative_sum_zero=> b _; exact: hc0.
rewrite hz hausdorff_diameter_cost_one_degree in hbound.
have hd := @metric_diameter_upper R X A _ (extended_metric_diameter_specification A)
  x y (or_introl (erefl x)) (or_intror (erefl y)).
have hbad := lt_le_trans (hxy : 0<(mdist x y)%:E) (le_trans hd hbound).
by rewrite ltxx in hbad.
Qed.
