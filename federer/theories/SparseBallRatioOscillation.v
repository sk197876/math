(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls LebesgueScalarMeasure WeightedHitMeasure
  SparseBallCoverSequenceUP SparseBallCoverRadii SparseWeightedHitBounds SparseScalarBallRatios
  ExtendedRealReciprocalBounds RealLatticeTruncationLimits PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sparse_high_ratio_arbitrarily_small]: direct
    cofinal high ratios in Federer 2.9.18(1), p. 163.
    Every positive radius cutoff contains a positive radius
    at which the ball ratio is exactly 1/2. *)
Lemma sparse_high_ratio_arbitrarily_small (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) :
  is_sparse_ball_cover_sequence T c S -> T x -> forall d : R, (0<d)%R ->
  exists r : R, (0<r<d)%R /\
    weighted_hit_measure c S (metric_closed_ball x r)/
      lebesgue_scalar_measure (metric_closed_ball x r)=((1/2)%R : R)%:E.
Proof.
move=> h hx d hd; have [N hN] := sparse_cover_radii_tend_zero h hd.
exists (c N.+1); split; last exact: sparse_scalar_high_radius_ratio h hx.
by apply/andP; split; [exact: sparse_cover_radius_positive h N.+1|exact: hN N.+1 (leqnSn N)].
Qed.

(** Source for [sparse_low_ratio_arbitrarily_small]: direct
    cofinal small ratios in Federer 2.9.18(1), p. 163.
    The scaled radii (n+1)c_(n+1) tend to zero and
    their ratios 1/(2(n+1)) lie below every prescribed
    positive epsilon. *)
Lemma sparse_low_ratio_arbitrarily_small (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) :
  is_sparse_ball_cover_sequence T c S -> T x -> forall d e : R, (0<d)%R -> (0<e)%R ->
  exists r : R, (0<r<d)%R /\
    weighted_hit_measure c S (metric_closed_ball x r)/
      lebesgue_scalar_measure (metric_closed_ball x r)<e%:E.
Proof.
move=> h hx d e hd he; have [N hN] := sparse_cover_radii_tend_zero h hd.
have [M hM] := positive_reciprocal_nat_small he.
pose n := maxn N M.
pose k := ((n.+1)%:R : R).
have hk : (0<k)%R by rewrite /k ltr0n.
have h2k : (0<2*k)%R by rewrite mulr_gt0 // ltr0n.
exists (k*c n.+1)%R; split.
- apply/andP; split; first by rewrite mulr_gt0 //; exact: sparse_cover_radius_positive h n.+1.
  apply: lt_trans (sparse_scaled_radius_below_current h n) _.
  exact: hN n (leq_maxl N M).
- rewrite (@sparse_scalar_low_radius_ratio R T c S x n h hx) lte_fin.
  have hhalf : (((2*k)%R)^-1<=k^-1)%R.
    rewrite (@lef_pV2 R (2*k)%R k h2k hk).
    by rewrite -{1}(mul1r k) (ler_pM2r hk) ler1n.
  apply: le_lt_trans hhalf _.
  exact: le_lt_trans (@positive_reciprocal_nat_antitone R M n (leq_maxr N M)) hM.
Qed.

(** Source for [sparse_ball_ratio_no_ordinary_limit]: direct
    failure of an ordinary radius limit in Federer 2.9.18(1),
    p. 163. Cofinal zero-approaching ratios rule out
    any positive limit, while cofinal ratios 1/2 rule out
    all nonpositive limits. Both extended infinities are included. *)
Theorem sparse_ball_ratio_no_ordinary_limit (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  ~ exists l : \bar R, positive_right_extended_order_limit
    (fun r => weighted_hit_measure c S (metric_closed_ball x r)/
      lebesgue_scalar_measure (metric_closed_ball x r)) l.
Proof.
move=> h hx [l [hlo hup]]; case: (ltP 0 l)=> [hl|hl].
- have [e [he heL]] : exists e : R, (0<e)%R /\ e%:E<l.
    clear hlo hup.
    case: l hl=> [a| |] ha.
    + exists (a/2)%R; split; first by rewrite divr_gt0 //; move: ha; rewrite lte_fin.
      rewrite lte_fin; have hp : (0<a)%R by move: ha; rewrite lte_fin.
      lra.
    + exists 1%R; split; [exact: ltr01|exact: ltry].
    + by move: ha; rewrite ltNge leNye.
  have [d [hd hb]] := hlo e%:E heL.
  have [r [/andP [hr hrd] hsmall]] := sparse_low_ratio_arbitrarily_small h hx hd he.
  by have := lt_trans (hb r hr hrd) hsmall; rewrite ltxx.
- have hquarter : (0<1/4 :> R)%R by rewrite divr_gt0 // ltr0n.
  have hquarterE : 0<((1/4)%R : R)%:E by rewrite lte_fin.
  have hupper : l<((1/4)%R : R)%:E := le_lt_trans hl hquarterE.
  have [d [hd hb]] := hup _ hupper.
  have [r [/andP [hr hrd] hhalf]] := sparse_high_ratio_arbitrarily_small h hx hd.
  have hbad := hb r hr hrd; rewrite hhalf lte_fin in hbad.
  have hreversed : (1/4<1/2 :> R)%R by rewrite ltr_pdivrMr ?ltr0n //; lra.
  by have := lt_trans hbad hreversed; rewrite ltxx.
Qed.
