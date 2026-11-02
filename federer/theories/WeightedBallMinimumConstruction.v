(** Private minimum witness for Federer (1969), 2.10.40, printed pp.
    199–200. Follow the printed infimum and nested-compact-set argument:
    sufficiently large scales are feasible, every scale strictly above the
    infimum is feasible, and reciprocal scales decrease to an attained
    minimum. The implementation is hidden by opaque sealing in the later
    interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  WeightedBallMinimumUP WeightedBallMinimumLaws WeightedBallFeasibleLaws
  WeightedBallParameterBounds CompactNestedIntersection ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_minimum_exists]: private
    existence and infimum-attainment argument of 2.10.40,
    pp. 199–200. The witness proves only the
    abstract feasibility and minimality laws; uniqueness
    and contact-centre membership are proved separately. *)
Theorem weighted_ball_minimum_exists (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o)) :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  exists D : weighted_ball_minimum_data R n, is_weighted_ball_minimum P D.
Proof.
move=> hP hne hpos.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have [t0 [ht0 hY0]] := @compact_weighted_ball_feasible_scale R n P hP hne hpos.
pose S := @weighted_ball_feasible_scales R n P.
have hSne : S !=set0.
  exists t0; split=> //; exists (0 : E); exact hY0.
have hlower : lbound S 0 by move=> t [ht _]; exact ht.
have hhas : has_lbound S by exists 0.
have hInf : has_inf S := conj hSne hhas.
pose c : R := inf S.
have hc : 0<=c := @lb_le_inf R S 0 hSne hlower.
have hYplus (e : R) : 0<e -> weighted_ball_centres P (c+e) !=set0.
  move=> he.
  have [t [ht [y hy]] htc] := @inf_adherent R S e he hInf.
  exists y; exact: (@weighted_ball_centres_monotone R n P t (c+e) hpos (ltW htc) y hy).
pose C k := @weighted_ball_centres R n P (c+(k.+1)%:R^-1).
have hepos k : 0<(k.+1)%:R^-1 :> R by rewrite invr_gt0 ltr0n.
have hCclosed k : closed (C k) := @weighted_ball_centres_closed R n P (c+(k.+1)%:R^-1).
have hCcompact : compact (C 0%N) := @weighted_ball_centres_compact R n P (c+1%:R^-1) hne.
have hCne k : C k !=set0 := hYplus _ (hepos k).
have hCdec k l (hkl : (k<=l)%N) : C l `<=` C k.
  apply: weighted_ball_centres_monotone hpos _.
  rewrite lerD2l.
  have hk : (0<k.+1%:R :> R) by rewrite ltr0n.
  have hl : (0<l.+1%:R :> R) by rewrite ltr0n.
  by rewrite (lef_pV2 hl hk) ler_nat.
have [b hb] := @compact_nested_nonempty_intersection [the topologicalType of E]
  C hCcompact hCclosed hCdec hCne.
have hfeasible : weighted_ball_centres P c b.
  move=> p hp.
  have hr := hpos p hp.
  rewrite leNgt; apply/negP=> hbad.
  have hgap : 0<(inner_norm (@euclidean_inner_productP R n) (b-p.1)-p.2*c)/p.2.
    by rewrite divr_gt0 // subr_gt0.
  have [k hk] := real_reciprocal_below hgap.
  have hmul : p.2*(k.+1)%:R^-1<inner_norm (@euclidean_inner_productP R n) (b-p.1)-p.2*c.
    rewrite mulrC -ltr_pdivlMr //; exact hk.
  have hh := hb k I p hp.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (b-p.1)<=p.2*(c+(k.+1)%:R^-1))) in hh.
  rewrite mulrDr in hh; rewrite ltrBrDl in hmul.
  have hfalse := le_lt_trans hh hmul; by rewrite ltxx in hfalse.
pose D : weighted_ball_minimum_data R n :=
  {| weighted_minimum_centre := b; weighted_minimum_scale := c |}.
exists D; constructor=> // t y ht hy.
exact (@ge_inf R S hhas t (conj ht (ex_intro _ y hy))).
Qed.
