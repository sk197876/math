(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra ring lra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationUP CoveringRelationFineness
  CoveringRelationLimits MetricDiameter CoveringLowerSublevel CoveringFiniteLimitBounds
  CoveringLipschitzFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [covering_lipschitz_family_domain_fine]: supporting domain
    qualification for the closedness assertion in Federer 2.9.9, p. 157 A
    finite limit at one parameter supplies arbitrarily small defined cells;
    the common-domain law transfers these cells to every parameter. *)
Lemma covering_lipschitz_family_domain_fine (R : realType) (X Y : metricType R)
    (V : X -> set X -> Prop) (u : Y -> partial_function (set X) (\bar R))
    (cap : R) x y z (a : R) :
  (0<cap)%R -> is_covering_lipschitz_family V u cap ->
  partial_function_graph (covering_relation_limit V (u y)) x a%:E ->
  covering_relation_fine_at (fun x S => V x S /\ partial_function_domain (u z) S) x.
Proof.
move=> hcap hu [_ [_ hl]].
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
have hp : (0<Num.min e cap)%R by rewrite lt_min he hcap.
have hb : covering_lower_limit V (u y) x<(a+1)%R%:E by rewrite hl lte_fin ltrDl ltr01.
have [S [v [hS [hd [hv _]]]]] := @covering_lower_limit_small_value R X V (u y) x
  (a+1)%R%:E (Num.min e cap) hb hp.
have hde : extended_metric_diameter S<e%:E.
  apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx.
have hdc : extended_metric_diameter S<cap%:E.
  apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx orbT.
exists S; split=> //; split=> //.
exact (@covering_family_common_domain R X Y V u cap hu x S hS hdc y z (ex_intro _ v hv)).
Qed.

Local Close Scope ereal_scope.

(** Source for [real_lipschitz_limit_transfer]: supporting scalar estimate
    in the closedness proof of Federer 2.9.9, p. 157 The two Lipschitz
    errors consume at most half the requested tolerance. *)
Lemma real_lipschitz_limit_transfer (R : realType) (a b l m d e : R) :
  (`|a-b|<=d -> `|m-l|<=d -> d<e/4 -> m-e/2<b -> b<m+e/2 ->
  l-e<a /\ a<l+e)%R.
Proof.
move=> hab hml hd hb1 hb2.
have hbm : `|b-m|<e/2.
  rewrite ltr_norml; apply/andP; split; lra.
have ha : `|a-l|<e.
  have heq : a-l=(a-b)+(b-m)+(m-l) by ring.
  rewrite heq.
  apply: le_lt_trans (ler_normD _ _) _.
  apply: le_lt_trans (lerD (ler_normD _ _) (lexx _)) _.
  apply: le_lt_trans (lerD (lerD hab (lexx _)) hml) _.
  have heq2 : (e/4+e/2+e/4=e)%R by lra.
  rewrite -heq2; exact: ltrD (ltrD hd hbm) hd.
move: ha; rewrite ltr_norml=> /andP [ha hb]; split; lra.
Qed.

Local Open Scope ereal_scope.

(** Source for [covering_lipschitz_limit_locus_closed]: supporting proof of
    Federer's assertion that T(x) is closed in 2.9.9, p. 157. The target
    value function is one-Lipschitz. No existence of a limit is assumed away
    from the closure of the agreement locus. *)
Theorem covering_lipschitz_limit_locus_closed (R : realType) (X Y : metricType R)
    (V : X -> set X -> Prop) (u : Y -> partial_function (set X) (\bar R))
    (cap : R) (l : Y -> R) x :
  (0<cap)%R -> is_covering_lipschitz_family V u cap ->
  (forall y z, (`|l y-l z|<=mdist y z)%R) ->
  closed [set y | partial_function_graph (covering_relation_limit V (u y)) x (l y)%:E].
Proof.
move=> hcap hu hl z hz.
have hnear (e : R) : (0<e)%R -> exists y,
    partial_function_graph (covering_relation_limit V (u y)) x (l y)%:E /\ (mdist z y<e)%R.
  move=> he; apply: (hz [set y | (mdist z y<e)%R]).
  apply: (metricType_numDomainType.nbhs_mdistP z _).2.
  by exists e.
have [w [hw _]] := hnear 1%R ltac:(by rewrite ltr01).
have hdf := @covering_lipschitz_family_domain_fine R X Y V u cap x w z (l w) hcap hu hw.
apply: (@covering_finite_limit_of_small_values R X V (u z) x (l z) hdf)=> e he.
have he4 : (0<e/4)%R by rewrite divr_gt0 // ltr0n.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have [y [hy hzy]] := hnear (e/4)%R he4.
have [d [hd hband]] := @covering_finite_limit_small_values R X V (u y) x (l y) (e/2)%R hy he2.
exists (Num.min d cap); split; first by rewrite lt_min hd hcap.
move=> S v hS hdiam hv.
have hdd : extended_metric_diameter S<d%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin ge_min lexx.
have hdc : extended_metric_diameter S<cap%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin ge_min lexx orbT.
have hvfin := @covering_family_finite R X Y V u cap hu x S hS hdc z v hv.
have hvreal : partial_function_graph (u z) S (fine v)%:E by rewrite fineK.
have [b hb] := @covering_family_common_domain R X Y V u cap hu x S hS hdc z y (ex_intro _ v hv).
have hbfin := @covering_family_finite R X Y V u cap hu x S hS hdc y b hb.
have hbreal : partial_function_graph (u y) S (fine b)%:E by rewrite fineK.
have hh := hband S (fine b)%:E hS hdd hbreal.
have hb1 : (l y-e/2<fine b)%R by move: hh.1; rewrite lte_fin.
have hb2 : (fine b<l y+e/2)%R by move: hh.2; rewrite lte_fin.
have hdiff := @covering_family_lipschitz R X Y V u cap hu x S hS hdc z y _ _ hvreal hbreal.
have htarget : (`|l y-l z|<=mdist z y)%R by rewrite (metric_sym z y); exact: hl.
have h := @real_lipschitz_limit_transfer R (fine v) (fine b) (l z) (l y) (mdist z y) e
  hdiff htarget hzy hb1 hb2.
by rewrite -(fineK hvfin) !lte_fin.
Qed.
