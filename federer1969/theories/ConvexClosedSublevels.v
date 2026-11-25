(** Federer (1969), 2.4.19, p. 91: the closed convex truncation sets C_n
    defined by simultaneous norm and F bounds. These supporting facts use
    only relative continuity on C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity MetricSubsetBackground
  RealMetricBackground MetricClosedBalls InnerConvex ConvexFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relative_continuous_sublevel_closed]: supporting closedness
    of the F sublevel inside C in Federer 2.4.19, p. 91 *)
Lemma relative_continuous_sublevel_closed (R : realType) (Y : metricType R)
    (C : set Y) (F : Y -> real_line_metric R) (t : R) :
  closed C -> continuous (fun y : metric_subset C => F (val y)) ->
  closed [set y | C y /\ F y <= t].
Proof.
move=> hC hF; have ho : open (~` [set y | C y /\ F y <= t]).
  rewrite openE=> x hx; case: (pselect (C x))=> hCx.
  - have ht : t < F x by rewrite ltNge; apply/negP=> hh; exact: hx (conj hCx hh).
    pose xx : metric_subset C := @exist Y (fun y => y \in C) x (mem_set hCx).
    have he : 0 < F x-t by rewrite subr_gt0.
    have hball : nbhs (F x) [set z : real_line_metric R | mdist (F x) z < F x-t].
      apply: (proj2 (metricType_numDomainType.nbhs_mdistP (F x) _)); by exists (F x-t).
    have [d hd hb] := proj1 (metricType_numDomainType.nbhs_mdistP xx _)(hF xx _ hball).
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)); exists d=> // y hy [hCy hFy].
    pose yy : metric_subset C := @exist Y (fun z => z \in C) y (mem_set hCy).
    have hh := @hb yy hy.
    change (is_true (`|F x-F y| < F x-t)) in hh.
    have hneg : -t <= - F y by rewrite lerN2.
    have hb' : F x-t <= `|F x-F y| := le_trans (lerD (lexx _) hneg) (ler_norm _).
    by have := le_lt_trans hb' hh; rewrite ltxx.
  - have hn : nbhs x (~` C) by have := closed_openC hC; rewrite openE=> h; exact: h x hCx.
    apply: filterS hn=> y hy [hCy _]; exact: hy hCy.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [relative_continuity_restrict]: supporting restriction of F
    to C_n in Federer 2.4.19, p. 91 *)
Lemma relative_continuity_restrict (R : realType) (Y : metricType R) (Z : topologicalType)
    (C D : set Y) (F : Y -> Z) : D `<=` C ->
  continuous (fun y : metric_subset C => F (val y)) ->
  continuous (fun y : metric_subset D => F (val y)).
Proof.
move=> hDC hF y U hU.
pose yy : metric_subset C := @exist Y (fun z => z \in C) (val y) (mem_set (hDC _ (set_valP y))).
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP yy _) (hF yy U hU).
apply: (proj2 (metricType_numDomainType.nbhs_mdistP y _)); exists e=> // z hz.
pose zz : metric_subset C := @exist Y (fun w => w \in C) (val z) (mem_set (hDC _ (set_valP z))).
exact: (@hb zz hz).
Qed.

(** Source for [convex_norm_function]: the norm bound in the convex set C_n
    of Federer 2.4.19, p. 91 Supporting consequence of the norm laws,
    without an inner-product hypothesis. *)
Lemma convex_norm_function (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) (C : set V) : is_inner_convex C -> is_real_convex_function_on C N.
Proof.
move=> hC; split=> // x y hx hy t ht ht1.
have h1t : 0 <= 1-t by rewrite subr_ge0.
have hh := real_seminorm_triangle hN.1 ((1-t) *: x) (t *: y).
by rewrite !(real_seminorm_scale hN.1) (ger0_norm h1t) (ger0_norm ht) in hh.
Qed.

(** Source for [convex_function_sublevel]: the convex F sublevel used in
    Federer 2.4.19, p. 91 *)
Lemma convex_function_sublevel (R : realType) (V : lmodType R)
    (C : set V) (F : V -> R) (a : R) : is_real_convex_function_on C F ->
  is_inner_convex [set y | C y /\ F y <= a].
Proof.
move=> hF x y [hx hFx] [hy hFy] t ht ht1; split; first exact: hF.1.
have h1t : 0 <= 1-t by rewrite subr_ge0.
apply: le_trans (hF.2 x y hx hy t ht ht1) _.
have hh := lerD (ler_wpM2l h1t hFx) (ler_wpM2l ht hFy).
by rewrite -mulrDl subrK mul1r in hh.
Qed.

(** Source for [jensen_closed_sublevel]: direct definition of C_n in Federer
    2.4.19, p. 91 A real threshold also permits cofinal shifted thresholds
    whose sets contain a fixed reference point. *)
Definition jensen_closed_sublevel (R : realType) (V : lmodType R)
    (N : V -> R) (C : set V) (F : V -> R) (a : R) :=
  [set y | C y /\ N y <= a /\ F y <= a].

(** Source for [jensen_sublevel_closed_convex]: verification of the closed
    convex sets asserted in Federer 2.4.19, p. 91 *)
Lemma jensen_sublevel_closed_convex (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN))
    (F : real_norm_metric_space hN -> real_line_metric R) (a : R) :
  closed C -> is_real_convex_function_on C F ->
  continuous (fun y : metric_subset C => F (val y)) ->
  closed (jensen_closed_sublevel N C F a : set (real_norm_metric_space hN)) /\ is_inner_convex (jensen_closed_sublevel N C F a).
Proof.
move=> hC hconv hF.
have hnorm : continuous (fun y : metric_subset C => (N (val y) : real_line_metric R)).
  move=> y U hU.
  exact: (@metric_subset_inclusion_continuous R (real_norm_metric_space hN) C y _
    (@real_norm_metric_norm_continuous R V N hN (val y) U hU)).
have hn := @relative_continuous_sublevel_closed R (real_norm_metric_space hN) C N a hC hnorm.
have hf := @relative_continuous_sublevel_closed R (real_norm_metric_space hN) C F a hC hF.
split.
- have he : jensen_closed_sublevel N C F a = [set y | C y /\ N y <= a] `&` [set y | C y /\ F y <= a].
    apply/seteqP; split=> y; by move=> [[? ?] [? ?]] || move=> [? [? ?]]; split=> //; split.
  rewrite he; exact: closedI hn hf.
- have hnconv := @convex_function_sublevel R V C N a (convex_norm_function hN hconv.1).
  have hfconv := @convex_function_sublevel R V C F a hconv.
  move=> x y [hx [hnx hfx]] [hy [hny hfy]] t ht ht1.
  have h1 := hnconv x y (conj hx hnx) (conj hy hny) t ht ht1.
  have h2 := hfconv x y (conj hx hfx) (conj hy hfy) t ht ht1.
  exact (conj h1.1 (conj h1.2 h2.2)).
Qed.
