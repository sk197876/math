(** Pass from separated parameters to disjointed ball families in Federer
    (1969), 2.8.12, p. 149, after condition (2). These consequences use only
    the decomposition laws and metric triangle inequality. Source context:
    BallFamilyDecompositionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls ControlledBallParameters
  RadiusCoverSelectionUP BallFamilyDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_parameters_give_disjoint_balls]:
    condition (1) implies disjointness of the associated closed
    balls in Federer 2.8.12, p. 149. No geodesic or normed
    structure is required. Supporting metric lemma. *)
Lemma separated_parameters_give_disjoint_balls (R : realType) (X : metricType R)
    (P : set (X*R)) : radius_parameters_separated P -> forall p q,
  P p -> P q -> p <> q -> parameter_closed_ball p `&` parameter_closed_ball q = set0.
Proof.
move=> hs p q hp hq hne; apply/seteqP; split=> [x [hpx hqx]|x []].
have hsep := hs p q hp hq hne.
have hsum : mdist p.1 q.1 <= p.2+q.2.
  apply: le_trans (metric_triangle p.1 x q.1) _.
  apply: lerD hpx _; by rewrite metric_sym.
by have := lt_le_trans hsep hsum; rewrite ltxx.
Qed.

(** Source for [parameter_decomposition_ball_families]: the
    last passage from the R_j to {B(a,r):(a,r) in R_j}
    in Federer 2.8.12, p. 149. Equal balls need not have
    unique general parameters: separation is applied to distinct
    members of a single color class. *)
Theorem parameter_decomposition_ball_families (R : realType) (X : metricType R)
    (Q : set (X*R)) (N : nat) (C : 'I_N -> set (X*R)) :
  is_radius_parameter_decomposition Q C ->
  is_disjoint_ball_family_decomposition (associated_closed_ball_family Q)
    (fun i => associated_closed_ball_family (C i)).
Proof.
move=> h; constructor.
- move=> i B [p hp <-]; exists p=> //.
  exact (@parameter_decomposition_members R X Q N C h i p hp).
- move=> i B D [p hp <-] [q hq <-] hne.
  have hpq : p <> q by move=> he; apply: hne; rewrite he.
  exact (@separated_parameters_give_disjoint_balls R X (C i)
    (@parameter_decomposition_separated R X Q N C h i) p q hp hq hpq).
- apply/seteqP; split.
  + move=> B [p hp <-].
    rewrite (parameter_decomposition_covers h) in hp.
    have [i hi hpi] := hp; exists i=> //; by exists p.
  + move=> B [i _ [p hp <-]]; exists p=> //.
    exact (@parameter_decomposition_members R X Q N C h i p hp).
Qed.
