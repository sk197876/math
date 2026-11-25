(** Federer (1969), 2.8.8, p. 145: if the weight is diameter, the
    enlargement of B(a,r) is contained in B[a,(1+2 tau)r]. The diameter is
    used only through its laws. Source context: DiametricRegularityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP WeightedEnlargements
  DiametricRegularityUP DiameterWeightLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diameter_enlargement_ball_bound]: direct formalisation of
    the closed-ball enlargement bound in Federer 2.8.8, p. 145 The
    supporting bound is valid already for tau>=0 and r>=0; the covering
    applications retain tau>1 and positive radii. *)
Theorem diameter_enlargement_ball_bound (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) (tau : R) :
  is_real_diameter_weight F d -> (0 <= tau)%R -> forall a r,
  F (metric_closed_ball a r) -> (0 <= r)%R ->
  weighted_enlargement F d tau (metric_closed_ball a r) `<=`
    metric_closed_ball a ((1+2*tau)*r)%R.
Proof.
move=> hd ht a r hS hr x [T [hT [hmeet hweight]] hx].
have hn : T `&` metric_closed_ball a r != set0 by apply/eqP.
have [y [hyT hyS]] := (set0P _).1 hn.
have hdist : (mdist y x <= d T)%R.
  have h := metric_diameter_upper (hd T hT) hyT hx.
  by rewrite lee_fin in h.
have hdS := @diameter_weight_ball_bound R X F d hd a r hS hr.
have hscaled := ler_wpM2l ht hdS.
have hdx := le_trans hdist (le_trans hweight hscaled).
have hax := le_trans (metric_triangle a y x) (lerD hyS hdx).
have he : (r + tau*(r+r) = (1+2*tau)*r)%R.
  by rewrite mulrDl mul1r mulrDr mulr_natl mulr2n mulrDl.
by rewrite /metric_closed_ball /= -he.
Qed.
