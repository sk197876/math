(** Diameter weights supporting Federer (1969), 2.8.8, p. 145. Consequences
    are derived from the abstract diameter specification, with existence
    supplied by the previously sealed extended diameter. Source context:
    DiametricRegularityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter
  CoveringFamilyUP DiametricRegularityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diameter_weight_nonnegative]: nonnegativity
    of the diameter weight in Federer 2.8.8, p. 145;
    supporting the use of 2.8.4–2.8.7. Empty sets have
    diameter zero under the existing project convention. *)
Lemma diameter_weight_nonnegative (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) :
  is_real_diameter_weight F d -> forall S, F S -> (0 <= d S)%R.
Proof.
move=> hd S hS; have h := metric_diameter_nonnegative (hd S hS).
by rewrite lee_fin in h.
Qed.

(** Source for [diameter_weight_ball_bound]: diam B(a,r) is at most 2r, the
    estimate used in the enlargement containment of Federer 2.8.8, p. 145 No
    equality with 2r is asserted in an arbitrary metric space. *)
Lemma diameter_weight_ball_bound (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) :
  is_real_diameter_weight F d -> forall a r,
  F (metric_closed_ball a r) -> (0 <= r)%R ->
  (d (metric_closed_ball a r) <= r+r)%R.
Proof.
move=> hd a r hF hr.
have h : (d (metric_closed_ball a r))%:E <= (r+r)%:E.
  apply: (metric_diameter_least (hd _ hF)).
  - by rewrite lee_fin addr_ge0.
  - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
by rewrite lee_fin in h.
Qed.

(** Source for [real_diameter_weight_exists]: existence of
    the finite diameter weight used in Federer 2.8.8,
    p. 145, on a family of bounded sets. Finiteness of
    the sealed extended diameter supplies a real representative;
    only its specification is used subsequently. *)
Theorem real_diameter_weight_exists (R : realType) (X : metricType R)
    (F : set (set X)) :
  (forall S, F S -> metric_set_bounded S) -> exists d, is_real_diameter_weight F d.
Proof.
move=> hb; pose d (S : set X) := fine (extended_metric_diameter S).
exists d=> S hS.
have hf : extended_metric_diameter S \is a fin_num.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative (extended_metric_diameter_specification S))).
  exact: hb S hS.
rewrite /d (fineK hf); exact: extended_metric_diameter_specification.
Qed.
