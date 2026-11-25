(** Federer (1969), 2.10.21, p. 184: convex functions form a closed subset
    of the cartesian product of real lines; hence the compact convex sets
    form a closed Hausdorff family. The erratum, p. 3, book p. 184 lines 8
    and 10, explicitly restricts the final density discussion to nonempty
    compact convex subsets. This file keeps that scope. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground RealNormUP NormMetric InnerConvex ConvexFunctionUP
  CompactSetDistanceProfile CompactConvexProfiles HausdorffProfileContinuity CompactHausdorffMetric
  CompactBallProfiles CompactHausdorffBall LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_real_order_constraint_closed]: supporting
    closed real comparison for convexity inequalities,
    2.10.21, p. 184. *)
Lemma continuous_real_order_constraint_closed (R : realType) (P : topologicalType)
    (f g : P -> R^o) : continuous f -> continuous g -> closed [set p | f p<=g p].
Proof.
move=> hf hg.
have hd : continuous (fun p : P => (f p-g p : R^o)).
  move=> p; exact: (@continuousB R R^o P f g p (hf p) (hg p)).
have he : [set p | f p<=g p]=(fun p : P => (f p-g p : R^o)) @^-1` [set t | t<=0].
  by apply/seteqP; split=> p hp; move: hp; rewrite /= subr_le0.
rewrite he; apply: preimage_closed; last exact: closed_le.
move=> p hp; exact: hd p.
Qed.

(** Source for [convex_real_profiles]: direct family
    of real convex functions in the last paragraph
    of 2.10.21, p. 184. *)
Definition convex_real_profiles (R : realType) (V : lmodType R) :
    set (prod_topology (fun _ : V => real_line_metric R)) :=
  [set f | is_real_convex_function_on setT f].

(** Source for [convex_real_profiles_closed]: direct
    closedness of real convex functions in 2.10.21,
    p. 184. Each fixed convexity inequality is
    a closed condition on three evaluations. *)
Theorem convex_real_profiles_closed (R : realType) (V : lmodType R) :
  closed (@convex_real_profiles R V).
Proof.
pose P := prod_topology (fun _ : V => real_line_metric R).
pose J := [the choiceType of ((V*V)*R)%type].
pose D : set J := [set p | 0<=p.2<=1].
pose A (p : J) : set P := [set f | f ((1-p.2)*:p.1.1+p.2*:p.1.2)<=
  (1-p.2)*f p.1.1+p.2*f p.1.2].
have he : @convex_real_profiles R V=\bigcap_(p in D) A p.
  apply/seteqP; split.
  - move=> f [_ hf] [[x y] t] /andP [ht ht1]; exact: hf x y I I t ht ht1.
  - move=> f hf; split; first by move=> x y hx hy t ht ht1.
    move=> x y hx hy t ht ht1.
    have hD : D ((x,y),t) by apply/andP; split.
    have hh : A ((x,y),t) f := hf ((x,y),t) hD.
    exact hh.
rewrite he; apply: closed_bigI=> p hp.
apply: (@continuous_real_order_constraint_closed R [the topologicalType of P]
  (fun f : P => (f ((1-p.2)*:p.1.1+p.2*:p.1.2) : R^o))
  (fun f : P => ((1-p.2)*f p.1.1+p.2*f p.1.2 : R^o))).
- exact: proj_continuous.
- move=> f.
  apply: (@continuousD R R^o P (fun g => (1-p.2)*g p.1.1) (fun g => p.2*g p.1.2) f).
  + apply: (@continuousM R P (fun _ => 1-p.2) (fun g => g p.1.1) f).
    * exact: (@cvg_cst [the topologicalType of R^o] (1-p.2) P (nbhs f) (nbhs_filter f)).
    * exact: (@proj_continuous V (fun _ : V => real_line_metric R) p.1.1 f).
  + apply: (@continuousM R P (fun _ => p.2) (fun g => g p.1.2) f).
    * exact: (@cvg_cst [the topologicalType of R^o] p.2 P (nbhs f) (nbhs_filter f)).
    * exact: (@proj_continuous V (fun _ : V => real_line_metric R) p.1.2 f).
Qed.

(** Source for [hausdorff_compact_convex_sets_closed]: direct
    Hausdorff closedness of nonempty compact convex sets
    in 2.10.21, p. 184. This supporting
    assertion holds without finite dimension. *)
Theorem hausdorff_compact_convex_sets_closed (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) :
  closed [set C : compact_hausdorff_space (real_norm_metric_space hN) | is_inner_convex (val C)].
Proof.
pose H := compact_hausdorff_space (real_norm_metric_space hN).
pose P := prod_topology (fun _ : V => real_line_metric R).
pose Q : H -> P := fun C => compact_set_distance_profile C.
have he : [set C : H | is_inner_convex (val C)]=Q @^-1` (@convex_real_profiles R V).
  apply/seteqP; split=> C hC.
  - exact: (proj1 (compact_convex_distance_profile C) hC).
  - exact: (proj2 (compact_convex_distance_profile C) hC).
rewrite he; apply: preimage_closed; last exact: convex_real_profiles_closed.
move=> C hC; exact: hausdorff_profile_continuous.
Qed.

(** Source for [compact_convex_sets_in_ball_compact]: direct
    compactness of convex members of F_(a,r),
    2.10.21, p. 184. The book assumes
    finite dimension; bounded compactness suffices here. *)
Theorem compact_convex_sets_in_ball_compact (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : V) (r : R) :
  metric_boundedly_compact (real_norm_metric_space hN) -> 0<=r ->
  compact [set C : compact_hausdorff_space (real_norm_metric_space hN) |
    is_inner_convex (val C) /\ @compact_sets_in_ball R (real_norm_metric_space hN) a r C].
Proof.
move=> hX hr.
have hball := @compact_hausdorff_ball_compact R (real_norm_metric_space hN) a r hX hr.
have hcl := @hausdorff_compact_convex_sets_closed R V N hN.
have hballcl := compact_closed (@metric_hausdorff R [the metricType R of
  compact_hausdorff_space (real_norm_metric_space hN)]) hball.
apply: (subclosed_compact (closedI hcl hballcl) hball)=> C [hc hC]; exact hC.
Qed.
