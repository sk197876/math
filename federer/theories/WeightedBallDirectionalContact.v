(** Federer (1969), 2.10.40, printed p. 200: let positive perturbations tend
    to zero, extracting a contact pair whose centre is on the nonpositive
    side of the chosen unit direction. Compactness is expressed by nested
    closed subsets of the given P. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric RealMetricBackground
  WeightedBallMinimumUP WeightedBallContactProfiles WeightedBallPerturbation
  CompactNestedIntersection ArchimedeanReciprocal ConvexProfileClosed HausdorffBinaryProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reciprocal_upper_bound_nonpositive]: supporting
    scalar limit in the contact-pair argument of
    2.10.40, p. 200. A real number bounded
    by every positive integer reciprocal is nonpositive. *)
Lemma reciprocal_upper_bound_nonpositive (R : realType) (x : R) :
  (forall k : nat, x<=(k.+1)%:R^-1) -> x<=0.
Proof.
move=> hx; rewrite leNgt; apply/negP=> hp.
have [k hk] := real_reciprocal_below hp.
have hfalse := le_lt_trans (hx k) hk; by rewrite ltxx in hfalse.
Qed.

(** Source for [weighted_ball_minimum_directional_contact]: direct
    limiting halfspace assertion in 2.10.40, p. 200.
    For each unit u there is a genuine contact
    centre a with u dot (a-b) nonpositive.
    The extracted pair remains in the original compact P. *)
Theorem weighted_ball_minimum_directional_contact (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n)
    (u : inner_metric_space (@euclidean_inner_productP R n)) :
  compact P -> P !=set0 -> positive_ball_parameter_family P -> is_weighted_ball_minimum P D ->
  euclidean_inner_product u u= 1 -> exists a,
    weighted_ball_contact_centres P (weighted_minimum_centre D) (weighted_minimum_scale D) a /\
    euclidean_inner_product u (a-weighted_minimum_centre D)<=0.
Proof.
move=> hP hne hpos hD hu.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose T := [the topologicalType of (E*R^o)%type].
pose b := weighted_minimum_centre D.
pose c := weighted_minimum_scale D.
pose e (k : nat) : R := (k.+1)%:R^-1.
pose Z k : set T := [set p | weighted_ball_slack b c p<=e k /\
  weighted_ball_direction u b p<=e k].
pose C k := P `&` Z k.
have hepos k : 0<e k by rewrite /e invr_gt0 ltr0n.
have hZclosed k : closed (Z k).
  apply: closedI.
  - apply: (@continuous_real_order_constraint_closed R T
      (fun p=>weighted_ball_slack b c p) (fun _=>e k)).
    + exact: weighted_ball_slack_continuous.
    + move=> p; exact: (@cvg_cst [the topologicalType of R^o] (e k) T (nbhs p) (nbhs_filter p)).
  - apply: (@continuous_real_order_constraint_closed R T
      (fun p=>weighted_ball_direction u b p) (fun _=>e k)).
    + exact: weighted_ball_direction_continuous.
    + move=> p; exact: (@cvg_cst [the topologicalType of R^o] (e k) T (nbhs p) (nbhs_filter p)).
have hPclosed : closed P.
  apply: (compact_closed _ hP).
  exact: hausdorff_binary_product (@metric_hausdorff R E)
    (@metric_hausdorff R [the metricType R of real_line_metric R]).
have hCclosed k : closed (C k) := closedI hPclosed (hZclosed k).
have hCcompact : compact (C 0%N) := compact_closedI hP (hZclosed 0%N).
have hCdec k l (hkl : (k<=l)%N) : C l `<=` C k.
  have he : e l<=e k.
    have hk : 0<k.+1%:R :> R by rewrite ltr0n.
    have hl : 0<l.+1%:R :> R by rewrite ltr0n.
    by rewrite /e (lef_pV2 hl hk) ler_nat.
  move=> p [hp [hs hd]]; split=> //; split; exact: le_trans _ he.
have hCne k : C k !=set0.
  have [p [hp hbad]] := @weighted_ball_minimum_perturbation_violates R n P D u (e k)
    hP hne hpos hD hu (hepos k).
  have [hs hd] := @weighted_ball_perturbation_profile_bounds R n P b u c (e k) p
    hpos (weighted_minimum_feasible_law hD) (weighted_minimum_scale_nonnegative_law hD)
    hu (hepos k) hp hbad.
  exists p; split=> //; split; first exact: ltW hs.
  have hehalf : e k/2<=e k by have := hepos k; nra.
  exact: le_trans (ltW hd) hehalf.
have [p hp] := @compact_nested_nonempty_intersection T C hCcompact hCclosed hCdec hCne.
have hpP : P p := (hp 0%N I).1.
have hs : weighted_ball_slack b c p<=0.
  apply: reciprocal_upper_bound_nonpositive=> k; exact: (hp k I).2.1.
have hd : weighted_ball_direction u b p<=0.
  apply: reciprocal_upper_bound_nonpositive=> k; exact: (hp k I).2.2.
have hfeasible := weighted_minimum_feasible_law hD hpP.
have hcontact : inner_norm (@euclidean_inner_productP R n) (b-p.1)=p.2*c.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact hfeasible.
  by move: hs; rewrite /weighted_ball_slack subr_le0.
exists p.1; split=> //; exists p.2; split=> //.
by rewrite -(surjective_pairing p).
Qed.
