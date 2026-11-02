(** Federer (1969), 2.10.40, printed p. 200: the contact family used in the
    convex-hull conclusion is nonempty. Prove this explicitly, including
    zero scale and ambient dimension zero. If all slacks were positive,
    compactness would give a uniform slack and permit a smaller feasible
    scale at the same centre. the uniform slack argument also covers the
    dimension-zero case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  WeightedBallMinimumUP WeightedBallParameterBounds WeightedBallContactProfiles CompactPositiveScalarBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_minimum_contacts_nonempty]: supporting
    nonempty contact family in 2.10.40, p. 200.
    A uniform slack would contradict the public least-
    scale law. No private minimum implementation is used. *)
Theorem weighted_ball_minimum_contacts_nonempty (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n) :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  is_weighted_ball_minimum P D ->
  weighted_ball_contact_centres P (weighted_minimum_centre D) (weighted_minimum_scale D) !=set0.
Proof.
move=> hP hne hpos hD.
pose b := weighted_minimum_centre D.
pose c := weighted_minimum_scale D.
change (weighted_ball_contact_centres P b c !=set0).
have hc := weighted_minimum_scale_nonnegative_law hD.
have hfeasible := weighted_minimum_feasible_law hD.
case: (eqVneq c 0)=> [hc0|hc0].
- have [[a r] hp] := hne.
  exists a,r; split=> //.
  have hh := hfeasible (a,r) hp.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (b-a)<=r*c)) in hh.
  rewrite hc0 mulr0 in hh; rewrite hc0 mulr0.
  apply/eqP; by rewrite eq_le hh (inner_norm_nonnegative _ _).
- have hcpos : 0<c by rewrite lt_neqAle eq_sym hc0 hc.
  apply: contrapT=> hnone.
  have hslackpos p : P p -> 0<weighted_ball_slack b c p.
    move=> hp; rewrite /weighted_ball_slack subr_gt0 lt_neqAle.
    apply/andP; split; last exact: hfeasible p hp.
    apply/eqP=> heq; apply: hnone.
    exists p.1,p.2; split; last exact heq.
    by case: p hp heq=> a r hp _.
  have [q [q' [hq [hq' [hd hbound]]]]] := @compact_positive_scalar_bounds R
    [the topologicalType of ((inner_metric_space (@euclidean_inner_productP R n))*R^o)%type]
    P (weighted_ball_slack b c) hne hP (@weighted_ball_slack_continuous R n b c) hslackpos.
  pose delta := weighted_ball_slack b c q.
  have hdelta : 0<delta := hd.
  have [lo [mu [_ [hmu hr]]]] := @compact_positive_ball_radius_bounds R n P hP hne hpos.
  have hmu0 : mu!=0 by rewrite (gt_eqF hmu).
  pose v := Order.min c (delta/mu).
  have hv : 0<v by rewrite /v lt_min hcpos divr_gt0.
  have hvc : v<=c by rewrite /v ge_min lexx.
  have hvd : v<=delta/mu by rewrite /v ge_min lexx orbT.
  pose e := v/2.
  have he : 0<e by rewrite /e divr_gt0 // ltr0n.
  have hev : e<=v by rewrite /e; lra.
  have hec : e<=c := le_trans hev hvc.
  have hvm : mu*v<=delta.
    have hh := ler_wpM2l (ltW hmu) hvd.
    by rewrite mulrCA mulfV ?mulr1 in hh.
  have hem : mu*e<=delta := le_trans (ler_wpM2l (ltW hmu) hev) hvm.
  have ht : 0<=c-e by rewrite subr_ge0.
  have hnew : weighted_ball_centres P (c-e) b.
    move=> p hp.
    have /andP [hs _] := hbound p hp.
    have hsl : delta<=p.2*c-inner_norm (@euclidean_inner_productP R n) (b-p.1) := hs.
    have /andP [_ hrp] := hr p hp.
    have hree : p.2*e<=delta := le_trans (ler_wpM2r (ltW he) hrp) hem.
    rewrite mulrBr lerBrDr.
    apply: le_trans (lerD (lexx _) hree) _.
    by move: hsl; rewrite lerBrDl.
  have hleast := @weighted_minimum_least_law R n P D hD (c-e) b ht hnew.
  have hstrict : c-e<c by rewrite ltrBlDr ltrDl.
  have hfalse := le_lt_trans hleast hstrict; by rewrite ltxx in hfalse.
Qed.
