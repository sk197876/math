(** Federer (1969), 2.10.21, p. 183: F_(a,r) is compact for the Hausdorff
    metric. Uniform profile control on the original compact ball controls
    the full Hausdorff distance by the two directed supremum identities.
    Transfer compactness of the closed profile image through this inverse
    continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile CompactBallProfiles
  CompactBallProfilesCompact LipschitzCompactConvergence LipschitzFunctionCompact
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance CompactHausdorffMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_profiles_ball_bound]: supporting
    equivalence of the profile and Hausdorff topologies
    on F_(a,r), 2.10.21, p. 183. Only
    values on the containing ball need to be controlled. *)
Lemma hausdorff_profiles_ball_bound (R : realType) (X : metricType R) (a : X) (r : R)
    (C D : compact_metric_set X) (e : R) :
  compact_sets_in_ball a r C -> compact_sets_in_ball a r D -> 0<=e ->
  (forall x, metric_closed_ball a r x ->
    `|compact_set_distance_profile C x-compact_set_distance_profile D x|<=e) ->
  hausdorff_distance C D<=e.
Proof.
move=> hC hD he hbound.
apply: (proj2 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) C D he)).
split=> x hx.
- have hh := hbound x (hC x hx).
  have hz := proj2 (compact_set_distance_profile_zero C x) hx.
  rewrite hz sub0r normrN in hh; exact: le_trans (ler_norm _) hh.
- have hh := hbound x (hD x hx).
  have hz := proj2 (compact_set_distance_profile_zero D x) hx.
  rewrite hz subr0 in hh; exact: le_trans (ler_norm _) hh.
Qed.

(** Source for [compact_ball_profile_inverse_neighborhood]: supporting
    inverse continuity of Omega on F_(a,r),
    2.10.21, p. 183. Finitely many product
    coordinates force any prescribed Hausdorff error. *)
Lemma compact_ball_profile_inverse_neighborhood (R : realType) (X : metricType R) (a : X) (r : R)
    (C : compact_metric_set X) (e : R) :
  metric_boundedly_compact X -> 0<=r -> compact_sets_in_ball a r C -> 0<e ->
  exists U, nbhs (compact_set_distance_profile C : prod_topology (fun _ : X => real_line_metric R)) U /\
    forall D, compact_sets_in_ball a r D -> U (compact_set_distance_profile D) -> hausdorff_distance C D<e.
Proof.
move=> hX hr hC he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [U [hU hbound]] := lipschitz_compact_uniform_neighborhood
  (compact_set_distance_profile_lipschitz C) (hX a r hr) he2.
exists U; split=> // D hD hUD.
have hl := hbound (compact_set_distance_profile D) hUD (compact_set_distance_profile_lipschitz D).
have hh : hausdorff_distance C D<=e/2.
  apply: (hausdorff_profiles_ball_bound hC hD (ltW he2))=> x hx.
  exact: ltW (hl x hx).
apply: le_lt_trans hh _; by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.

(** Source for [compact_hausdorff_ball_compact]: direct
    compactness of F_(a,r) in 2.10.21,
    p. 183. Radius zero is included in the
    supporting result; positive radii recover the printed case. *)
Theorem compact_hausdorff_ball_compact (R : realType) (X : metricType R) (a : X) (r : R) :
  metric_boundedly_compact X -> 0<=r ->
  compact [set C : compact_hausdorff_space X | compact_sets_in_ball a r C].
Proof.
move=> hX hr.
pose P := prod_topology (fun _ : X => real_line_metric R).
pose A : set P := compact_ball_profiles a r.
pose H := compact_hausdorff_space X.
pose z : H := exist _ [set a] (mem_set (conj (@compact_set1 X a) (ex_intro _ a erefl))).
pose pick (f : P) : H :=
  if pselect (exists C : H, compact_sets_in_ball a r C /\ f=compact_set_distance_profile C)
    is left h then sval (cid h) else z.
have hp f (hf : A f) : compact_sets_in_ball a r (pick f) /\ f=compact_set_distance_profile (pick f).
  rewrite /pick; case: pselect=> [h|h]; first exact: svalP (cid h).
  exfalso; apply: h; exact hf.
have hg : {within A, continuous pick}.
  apply/subspace_continuousP=> f hf W hW.
  have [e he hball] := (metricType_numDomainType.nbhs_mdistP (pick f) W).1 hW.
  have [hCf hfC] := hp f hf.
  have [U [hU hbound]] := compact_ball_profile_inverse_neighborhood hX hr hCf he.
  rewrite -hfC in hU.
  change (nbhs f [set g | A g -> W (pick g)]).
  apply: (filterS _ hU)=> g hUg hAg.
  have [hCg hgC] := hp g hAg.
  apply: hball; change (is_true (hausdorff_distance (pick f) (pick g)<e)).
  apply: (hbound (pick g) hCg); by rewrite -hgC.
have heq : (pick @` A)=[set C : H | compact_sets_in_ball a r C].
  apply/seteqP; split.
  - move=> C [f hf <-]; exact: (hp f hf).1.
  - move=> C hC; exists (compact_set_distance_profile C).
    + exists C; by split.
    + apply: compact_set_distance_profile_injective.
      have hh := (hp (compact_set_distance_profile C) (ex_intro _ C (conj hC erefl))).2.
      exact: esym hh.
rewrite -heq.
exact: (@continuous_compact [the topologicalType of P] [the topologicalType of H] pick A hg
  (@compact_ball_profiles_compact R X a r hX hr)).
Qed.
