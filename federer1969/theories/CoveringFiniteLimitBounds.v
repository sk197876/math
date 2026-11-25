(** Finite limit estimates for the signed step in Federer (1969), 2.9.8, p.
    156, using the covering-limit definitions 2.8.16, p. 151. These
    supporting lemmas isolate its finite-value case and retain graph
    domains, including the required restricted fineness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationUP CoveringRelationFineness
  CoveringRelationLimits MetricDiameter ExtendedRealBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_lower_limit_gt_iff]: supporting
    eventual strict lower bound for the signed
    difference step in Federer 2.9.8, p. 156.
    It is the supremum dual of the existing
    upper-limit criterion for 2.8.16, p. 151. *)
Lemma covering_lower_limit_gt_iff (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x b :
  b<covering_lower_limit V f x <->
    exists e : R, (0<e)%R /\ b<extended_real_inf (covering_value_range V f x e).
Proof.
split.
- move=> hl; apply: contrapT=> hn.
  have hle : covering_lower_limit V f x<=b.
    apply: extended_real_sup_least=> y [e [he ->]].
    rewrite leNgt; apply/negP=> h; apply: hn; by exists e.
  by have := lt_le_trans hl hle; rewrite ltxx.
- move=> [e [he hh]]; exact: lt_le_trans hh (@covering_lower_limit_ge_level R X V f x e he).
Qed.

(** Source for [covering_finite_limit_small_values]: supporting epsilon
    bounds for the finite limits in the signed case of Federer 2.9.8, p. 156
    Values are bounded only where their partial graph is defined; domain
    existence is separate. *)
Lemma covering_finite_limit_small_values (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x (c e : R) :
  partial_function_graph (covering_relation_limit V f) x c%:E -> (0<e)%R ->
  exists d : R, (0<d)%R /\ forall S y, V x S -> extended_metric_diameter S<d%:E ->
    partial_function_graph f S y -> (c-e)%R%:E<y /\ y<(c+e)%R%:E.
Proof.
move=> [_ [hu hl]] he.
have hup : covering_upper_limit V f x<(c+e)%R%:E by rewrite hu lte_fin ltrDl.
have hlo : (c-e)%R%:E<covering_lower_limit V f x by rewrite hl lte_fin ltrBlDr ltrDl.
have [a [ha hsup]] := (covering_upper_limit_lt_iff V f x _).1 hup.
have [b [hb hinf]] := (covering_lower_limit_gt_iff V f x _).1 hlo.
exists (Num.min a b); split; first by rewrite lt_min ha hb.
move=> S y hS hd hy.
have hda : extended_metric_diameter S<a%:E.
  apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx.
have hdb : extended_metric_diameter S<b%:E.
  apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx orbT.
have hva : covering_value_range V f x a y by exists S; split=> //; split.
have hvb : covering_value_range V f x b y by exists S; split=> //; split.
split; [exact: lt_le_trans hinf (extended_real_inf_lower hvb)|exact: le_lt_trans (extended_real_sup_upper hva) hsup].
Qed.

(** Source for [covering_finite_limit_of_small_values]: supporting finite
    limit criterion for the signed conclusion of Federer 2.9.8, p. 156.
    Restricted domain fineness is explicit, as emphasised. Epsilon estimates
    alone do not fill an empty graph. *)
Lemma covering_finite_limit_of_small_values (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x (c : R) :
  covering_relation_fine_at (fun x S => V x S /\ partial_function_domain f S) x ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\ forall S y,
    V x S -> extended_metric_diameter S<d%:E -> partial_function_graph f S y ->
    (c-e)%R%:E<y /\ y<(c+e)%R%:E) ->
  partial_function_graph (covering_relation_limit V f) x c%:E.
Proof.
move=> hdf hsmall.
have hupper : covering_upper_limit V f x<=c%:E.
  apply: extended_real_reciprocal_upper_bound=> n.
  pose e := ((n.+1%:R : R)^-1)%R.
  have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
  have [d [hd hb]] := hsmall e he.
  have hsup : extended_real_sup (covering_value_range V f x d)<=(c+e)%R%:E.
    apply: extended_real_sup_least=> y [S [hS [hdiam hy]]]; exact: ltW (hb S y hS hdiam hy).2.
  exact: le_trans (@covering_upper_limit_le_level R X V f x d hd) hsup.
have hnegative : -covering_lower_limit V f x<=(-c)%R%:E.
  apply: extended_real_reciprocal_upper_bound=> n.
  pose e := ((n.+1%:R : R)^-1)%R.
  have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
  have [d [hd hb]] := hsmall e he.
  have hinf : (c-e)%R%:E<=extended_real_inf (covering_value_range V f x d).
    apply: extended_real_inf_greatest=> y [S [hS [hdiam hy]]]; exact: ltW (hb S y hS hdiam hy).1.
  have hle := le_trans hinf (@covering_lower_limit_ge_level R X V f x d hd).
  have hneg : -covering_lower_limit V f x<=-((c-e)%R%:E) by rewrite leeN2.
  by rewrite -EFinN opprB addrC in hneg.
have hlower : c%:E<=covering_lower_limit V f x by move: hnegative; rewrite EFinN leeN2.
have horder := @covering_limits_ordered R X V f x hdf.
have hu : covering_upper_limit V f x=c%:E.
  apply/eqP; by rewrite eq_le hupper (le_trans hlower horder).
have hl : covering_lower_limit V f x=c%:E.
  apply/eqP; by rewrite eq_le hlower andbT (le_trans horder hupper).
split.
- exact (@covering_relation_fine_mono R X (fun x S => V x S /\ partial_function_domain f S) V x
    (fun S h => h.1) hdf).
- by split.
Qed.
