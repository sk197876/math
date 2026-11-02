(** Federer (1969), 2.10.2(1), p. 171, final sentence about normed vector
    spaces: restricting covers to convex sets leaves the Hausdorff measure
    unchanged. Use the abstract hull and the proved diameter identity, with
    no finite-dimensionality premise. This file concerns the printed
    nonnegative integer degrees; the optional real-degree Gamma extension is
    separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import InnerConvex ConvexHull RealNormUP NormMetric
  NormConvexHullDiameter HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  MetricDiameter CaratheodoryTransport CaratheodoryMeasure CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonempty_convex_sets]: supporting admissible
    family for the convex-cover alternative in Federer
    2.10.2(1), p. 171. Convexity uses the given vector
    space, independently of its norm or a hull construction. *)
Definition nonempty_convex_sets (R : realFieldType) (V : lmodType R) :=
  [the choiceType of set_type [set A : set V | A !=set0 /\ is_inner_convex A]].

(** Source for [nonempty_convex_hull]: supporting replacement
    of each nonempty generator by its convex hull in
    Federer 2.10.2(1), p. 171. *)
Definition nonempty_convex_hull (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (j : @nonempty_metric_sets R (real_norm_metric_space hN)) :
    nonempty_convex_sets V.
Proof.
apply: (@exist _ (fun A : set V => A \in [set A | A !=set0 /\ is_inner_convex A])
  (@convex_hull R V (val j))); apply: mem_set; split.
- have [x hx] := set_valP j; exists x; exact: (@convex_hull_includes R V (val j) x hx).
- exact: convex_hull_convex.
Defined.

(** Source for [nonempty_convex_forget]: supporting reverse
    inclusion of covering families in Federer 2.10.2(1),
    p. 171: a nonempty convex set is a nonempty set. *)
Definition nonempty_convex_forget (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (j : nonempty_convex_sets V) :
    @nonempty_metric_sets R (real_norm_metric_space hN) :=
  @exist _ (fun A : set (real_norm_metric_space hN) => A \in [set A | A !=set0])
    (val j) (mem_set (set_valP j).1).

(** Source for [is_convex_hausdorff_measure]: abstract
    convex-cover version of Federer 2.10.2(1), p. 171. *)
Definition is_convex_hausdorff_measure (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (m : nat)
    (mu : set (real_norm_metric_space hN) -> \bar R) : Prop :=
  is_caratheodory_limit (fun j : nonempty_convex_sets V => (val j : set (real_norm_metric_space hN)))
    (fun j => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j)) mu.

(** Source for [convex_hausdorff_cover_agreement]: direct
    equality with convex covers in Federer 2.10.2(1),
    p. 171, using hulls in one direction and forgetting
    convexity in the other. Both measures are specified
    independently by their covering laws. *)
Theorem convex_hausdorff_cover_agreement (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (m : nat)
    (mu nu : set (real_norm_metric_space hN) -> \bar R) :
  is_hausdorff_measure m mu -> @is_convex_hausdorff_measure R V N hN m nu ->
  forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hc : nu (id @` A)<=mu A.
  apply: (@caratheodory_limit_transport R (real_norm_metric_space hN) (real_norm_metric_space hN)
    (@nonempty_metric_sets R (real_norm_metric_space hN)) (nonempty_convex_sets V)
    (fun j => (val j : set (real_norm_metric_space hN))) (fun j => (val j : set (real_norm_metric_space hN)))
    (fun j => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j))
    (fun j => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j)) id (@nonempty_convex_hull R V N hN)
    mu nu hm hn _ _ _ _ A).
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - move=> j x hx; exact: (@convex_hull_includes R V (val j) x hx).
  - move=> j; change (@extended_metric_diameter R (real_norm_metric_space hN) (@convex_hull R V (val j))<=@extended_metric_diameter R (real_norm_metric_space hN) (val j)).
    by rewrite (@extended_metric_diameter_convex_hull R V N hN).
  - move=> j; change (@hausdorff_diameter_cost R (real_norm_metric_space hN) m (@convex_hull R V (val j))<=@hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j)).
    by rewrite /hausdorff_diameter_cost (@extended_metric_diameter_convex_hull R V N hN).
have ha : mu (id @` A)<=nu A.
  apply: (@caratheodory_limit_transport R (real_norm_metric_space hN) (real_norm_metric_space hN)
    (nonempty_convex_sets V) (@nonempty_metric_sets R (real_norm_metric_space hN))
    (fun j => (val j : set (real_norm_metric_space hN))) (fun j => (val j : set (real_norm_metric_space hN)))
    (fun j => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j))
    (fun j => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j)) id (@nonempty_convex_forget R V N hN)
    nu mu hn hm _ _ _ _ A).
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
rewrite image_id in hc ha.
by apply/eqP; rewrite eq_le ha hc.
Qed.

(** Source for [hausdorff_convex_cover_specification]: direct
    assertion that the usual Hausdorff measure is obtained
    from convex covers in Federer 2.10.2(1), p. 171.
    Existence of the competing infimum is supplied by the
    sealed general Caratheodory construction. *)
Theorem hausdorff_convex_cover_specification (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (m : nat) :
  @is_convex_hausdorff_measure R V N hN m (@hausdorff_measure R (real_norm_metric_space hN) m).
Proof.
pose S := fun j : nonempty_convex_sets V => (val j : set (real_norm_metric_space hN)).
pose c := fun j : nonempty_convex_sets V => @hausdorff_diameter_cost R (real_norm_metric_space hN) m (val j).
pose nu := caratheodory_measure S c.
have hn : @is_convex_hausdorff_measure R V N hN m nu := caratheodory_measure_specification S c.
have he : @hausdorff_measure R (real_norm_metric_space hN) m=nu.
  apply: funext=> A; exact (@convex_hausdorff_cover_agreement R V N hN m _ _
    (@hausdorff_measure_specification R (real_norm_metric_space hN) m) hn A).
by rewrite he.
Qed.
