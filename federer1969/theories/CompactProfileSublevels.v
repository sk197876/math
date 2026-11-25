(** Federer (1969), 2.10.21, p. 183: the sublevel sets D_epsilon of a
    closure profile are compact; their intersection D_0 is nonempty and lies
    in the original ball. Use reciprocal positive levels to express the
    printed decreasing compact argument through the existing neighbourhood
    lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactBallProfiles CompactSetDistanceProfile
  MetricSetDistanceBasic LipschitzUP LipschitzFunctionCompact NormMetricScaleContinuity
  CompactDecreasingNeighborhoods ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closure_profile_continuous]: supporting
    continuity of f in 2.10.21, p. 183,
    since closure retains its Lipschitz bound one. *)
Lemma closure_profile_continuous (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) :
  closure (compact_ball_profiles a r) f -> continuous f.
Proof.
move=> hf; have hLip := (compact_ball_profile_closure_laws hf).1.
apply: (@metric_fixed_lipschitz_continuous R X [the metricType R of real_line_metric R] f 1 hLip.1).
move=> x y; exact: hLip.2 x y I I.
Qed.

(** Source for [closure_profile_sublevel_closed]: supporting
    closedness of D_epsilon in 2.10.21, p. 183. *)
Lemma closure_profile_sublevel_closed (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) (e : R) :
  closure (compact_ball_profiles a r) f -> closed [set x | f x<=e].
Proof.
move=> hf; apply: (@preimage_closed X (real_line_metric R) f [set y | y<=e]).
- move=> x hx; exact: closure_profile_continuous hf x.
- exact: closed_le.
Qed.

(** Source for [closure_profile_sublevel_compact]: direct
    D_epsilon subset B(a,r+epsilon) and compactness
    in 2.10.21, p. 183. Zero levels are included. *)
Lemma closure_profile_sublevel_compact (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) (e : R) :
  metric_boundedly_compact X -> 0<=r -> 0<=e ->
  closure (compact_ball_profiles a r) f -> compact [set x | f x<=e].
Proof.
move=> hX hr he hf.
have hclosed := @closure_profile_sublevel_closed R X a r f e hf.
have hball := hX a (r+e) (addr_ge0 hr he).
apply: (subclosed_compact hclosed hball)=> x hx.
have hh := (compact_ball_profile_closure_laws hf).2.2 x.
change (is_true (mdist a x<=r+e)); change (is_true (f x<=e)) in hx; lra.
Qed.

(** Source for [closure_profile_positive_sublevel_nonempty]: direct
    nonemptiness of positive D_epsilon in 2.10.21,
    p. 183. Approximate uniformly on the original
    ball and choose a member of the approximating set. *)
Lemma closure_profile_positive_sublevel_nonempty (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) (e : R) :
  metric_boundedly_compact X -> 0<=r -> 0<e ->
  closure (compact_ball_profiles a r) f -> [set x | f x<=e] !=set0.
Proof.
move=> hX hr he hf.
have [C [hC hbound]] := compact_ball_profile_closure_approximation hf (hX a r hr) he.
have [c hc] := (set_valP C).2.
have hh := hbound c (hC c hc).
have hz := proj2 (compact_set_distance_profile_zero C c) hc.
rewrite hz subr0 in hh.
exists c; exact: le_trans (ler_norm _) (ltW hh).
Qed.

(** Source for [closure_profile_reciprocal_intersection]: supporting
    countable expression for D_0 in 2.10.21,
    p. 183. Nonnegativity excludes negative values;
    reciprocal levels exclude every strictly positive value. *)
Lemma closure_profile_reciprocal_intersection (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) :
  closure (compact_ball_profiles a r) f ->
  (\bigcap_n [set x | f x<=n.+1%:R^-1])=[set x | f x=0].
Proof.
move=> hf; apply/seteqP; split=> x hx.
- have h0 := (compact_ball_profile_closure_laws hf).2.1 x.
  apply/eqP; rewrite eq_le h0 andbT.
  case: (leP (f x) 0)=> // hpos.
  have [n hn] := real_reciprocal_below hpos.
  have hh := le_lt_trans (hx n I) hn; by rewrite ltxx in hh.
- move=> n _; change (is_true (f x<=n.+1%:R^-1)); rewrite hx.
  have hp : (0<n.+1%:R^-1 :> R) by rewrite invr_gt0 ltr0n.
  exact: ltW hp.
Qed.

(** Source for [closure_profile_zero_set_compact_nonempty]: direct
    nonempty compact D_0 in F_(a,r) in
    2.10.21, p. 183. The decreasing compact
    principle is proved even when an intersection might
    be empty, so nonemptiness here is a conclusion. *)
Theorem closure_profile_zero_set_compact_nonempty (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) :
  metric_boundedly_compact X -> 0<=r -> closure (compact_ball_profiles a r) f ->
  compact [set x | f x=0] /\ [set x | f x=0] !=set0 /\
    [set x | f x=0] `<=` metric_closed_ball a r.
Proof.
move=> hX hr hf.
pose C (n : nat) : set X := [set x | f x<=n.+1%:R^-1].
have hpos n : (0<n.+1%:R^-1 :> R) by rewrite invr_gt0 ltr0n.
have hclosed n : closed (C n) := @closure_profile_sublevel_closed R X a r f n.+1%:R^-1 hf.
have hcompact n : compact (C n) := closure_profile_sublevel_compact hX hr (ltW (hpos n)) hf.
have hne n : C n !=set0 := closure_profile_positive_sublevel_nonempty hX hr (hpos n) hf.
have hdec n m (hnm : (n<=m)%N) : C m `<=` C n.
  move=> x hx; apply: le_trans hx _.
  have hn0 : (0<n.+1%:R :> R) by rewrite ltr0n.
  have hm0 : (0<m.+1%:R :> R) by rewrite ltr0n.
  have hcast : (n.+1%:R<=m.+1%:R :> R) by rewrite ler_nat.
  by rewrite (lef_pV2 hm0 hn0).
have he := closure_profile_reciprocal_intersection hf.
have hZ : [set x | f x=0]=[set x | f x<=0].
  apply/seteqP; split=> x hx; first by change (is_true (f x<=0)); rewrite hx.
  apply/eqP; by rewrite eq_le hx (compact_ball_profile_closure_laws hf).2.1.
split.
- rewrite hZ; exact: closure_profile_sublevel_compact hX hr (lexx 0) hf.
split.
- apply: contrapT=> hnone.
  have hK : (\bigcap_n C n) `<=` set0.
    move=> x hx; apply: hnone; exists x; by rewrite -he.
  have [N hN] := @compact_decreasing_eventually_in_open X C set0
    (hcompact 0%N) hclosed hdec open0 hK.
  have [x hx] := hne N; exact: hN N (leqnn N) x hx.
- move=> x hx.
  have hh := (compact_ball_profile_closure_laws hf).2.2 x.
  rewrite hx in hh; change (is_true (mdist a x<=r)); lra.
Qed.
