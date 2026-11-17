(** Federer 2.10.27, p. 191: the actual real radial power integral.
    Positive segment primitives and increasing reciprocal cutoffs give
    the endpoint at zero. The real degree may be less than one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground RealPower RealPowerPositiveSegmentIntegral
  RealPowerReciprocalLimit RealPowerContinuity HausdorffFibreCutoffs StieltjesIntegral
  ExtendedRealOrderLimit RealScalarOrderLimits RealIncreasingIntegralLimit
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  SummableRealFunctionUP RealSubsetIntegralGraph LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_radius_power]: supporting radial integrand
    for Federer 2.10.27, p. 191, equal to x^(p-1) on 0<x<=r and
    zero elsewhere. Its value at zero is fixed before integration. *)
Definition positive_radius_power (R : realType) (p r x : R) : R :=
  if (0 < x <= r) then real_power x (p-1) else 0.

(** Source for [reciprocal_radius_power_cutoff]: supporting positive
    segment exhaustion for the radial integral of Federer 2.10.27,
    p. 191. Keep the upper endpoint and let the lower endpoint decrease. *)
Definition reciprocal_radius_power_cutoff (R : realType) (p r : R)
    (n : nat) (x : R) : R :=
  if (r*(n.+1%:R)^-1 <= x <= r) then real_power x (p-1) else 0.

(** Source for [positive_radius_power_nonnegative]: nonnegativity
    of the radial integrand used in Federer 2.10.27, p. 191. *)
Lemma positive_radius_power_nonnegative (R : realType) (p r x : R) :
  0 <= positive_radius_power p r x.
Proof. rewrite /positive_radius_power; case: ifP=> _; [exact: real_power_nonnegative|exact: lexx]. Qed.

(** Source for [reciprocal_radius_power_eventually]: supporting
    pointwise endpoint passage for Federer 2.10.27, p. 191. At each
    point the reciprocal segment functions eventually equal the original
    radial function, including both excluded and retained endpoints. *)
Lemma reciprocal_radius_power_eventually (R : realType) (p r x : R) :
  0 < r -> exists N : nat, forall n, (N <= n)%N ->
    reciprocal_radius_power_cutoff p r n x = positive_radius_power p r x.
Proof.
move=> hr; case hpoint: (0 < x <= r).
- have /andP [hx hxr] := hpoint.
  have [N hN] := @uniform_mesh_small R 0 r x (ltW hr) hx.
  exists N=> n hn.
  have hsmall : r*(n.+1%:R)^-1 < x.
    have h := hN n hn; by rewrite subr0 in h.
  by rewrite /reciprocal_radius_power_cutoff /positive_radius_power
    hpoint (ltW hsmall) hxr.
- exists 0%N=> n _.
  rewrite /reciprocal_radius_power_cutoff /positive_radius_power hpoint.
  case: ifP=> hcut; last by [].
  have /andP [hl hu] := hcut.
  have hlow : 0 < r*(n.+1%:R)^-1 by rewrite mulr_gt0 // invr_gt0 ltr0n.
  have hgood : 0 < x <= r by rewrite (lt_le_trans hlow hl) hu.
  by rewrite hgood in hpoint.
Qed.

(** Source for [positive_radius_power_integral]: the real power
    integral r^p/p underlying the profile evaluation in Federer
    2.10.27, p. 191, with every real p>0 and r>0. Neither
    integrability at zero nor an improper integral is a premise. *)
Theorem positive_radius_power_integral (R : realType) (p r : R) :
  0 < p -> 0 < r ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (positive_radius_power p r)) (p^-1*real_power r p)%:E.
Proof.
move=> hp hr.
pose f := @reciprocal_radius_power_cutoff R p r.
pose a n := (p^-1*real_power r p-p^-1*real_power (r*(n.+1%:R)^-1) p).
have hinvpos n : (0 < (n.+1%:R : R)^-1) by rewrite invr_gt0 ltr0n.
have hinvle n : ((n.+1%:R : R)^-1 <= 1).
  have h := @fibre_reciprocal_cutoff_antitone R 0 n (leq0n n).
  by rewrite /= invr1 in h.
have hsegment n : 0 < r*(n.+1%:R)^-1 <= r.
  apply/andP; split.
  - by rewrite mulr_gt0 // invr_gt0 ltr0n.
  - have h := ler_wpM2l (ltW hr) (hinvle n).
    by rewrite mulr1 in h.
have hnon n x : 0 <= f n x.
  rewrite /f /reciprocal_radius_power_cutoff; case: ifP=> _;
    [exact: real_power_nonnegative|exact: lexx].
have hinc n x : f n x <= f n.+1 x.
  have h := @fibre_reciprocal_cutoff_antitone R n n.+1 (leqnSn n).
  have hcut := ler_wpM2l (ltW hr) h.
  rewrite /f /reciprocal_radius_power_cutoff.
  case: ifP=> [/andP [hl hu]|hnot].
  - by rewrite (le_trans hcut hl) hu lexx.
  - case: ifP=> _; [exact: real_power_nonnegative|exact: lexx].
have hpoint x : extended_order_limit (fun n => (f n x)%:E)
    (positive_radius_power p r x)%:E.
  have [N hN] := @reciprocal_radius_power_eventually R p r x hr.
  split=> b hb; exists N=> n hn; by rewrite /f hN.
have hi n : is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (f n)) (a n)%:E.
  have hI := @positive_real_power_segment_integral R p (r*(n.+1%:R)^-1) r
    hp (andP (hsegment n)).1 (andP (hsegment n)).2.
  apply: ((@real_subset_integral_total R R (@lebesgue_scalar_measure R)
    `[r*(n.+1%:R)^-1,r] (fun x => real_power x (p-1)) (f n) (a n)%:E _ _).1 hI).
  - move=> x; rewrite /= in_itv /= => hx.
    by rewrite /f /reciprocal_radius_power_cutoff hx.
  - move=> x hx; rewrite /f /reciprocal_radius_power_cutoff.
    case: ifP=> h; last by [].
    exfalso; apply: hx; by rewrite /= in_itv /=.
have hPower := @real_scalar_order_limit R
  (fun n => real_power (n.+1%:R)^-1 p) 0 (real_power r p)
  (@positive_real_power_reciprocal_limit R p hp).
rewrite mulr0 in hPower.
have hPowerScaled : extended_order_limit
    (fun n => (real_power (r*(n.+1%:R)^-1) p)%:E) 0%E.
  have he : (fun n => (real_power (r*(n.+1%:R)^-1) p)%:E) =
      (fun n => (real_power r p*real_power (n.+1%:R)^-1 p)%:E).
    apply: funext=> n; by rewrite real_power_product ?(ltW hr) ?(ltW (hinvpos n)).
  by rewrite he.
have hValues := @real_affine_order_limit R
  (fun n => real_power (r*(n.+1%:R)^-1) p) 0 (-p^-1) (p^-1*real_power r p) hPowerScaled.
rewrite mulr0 addr0 in hValues.
have hEq : (fun n => ((p^-1*real_power r p)+(-p^-1)*real_power (r*(n.+1%:R)^-1) p)%R%:E) =
    (fun n => (a n)%:E).
  by apply: funext=> n; rewrite /a mulNr.
rewrite hEq in hValues.
exact: (@real_nonnegative_increasing_integral_limit R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) f (positive_radius_power p r) (fun n => (a n)%:E)
  (p^-1*real_power r p)%:E hnon hinc hpoint hi hValues).
Qed.
