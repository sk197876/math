(** Federer (1969), 3.2.16, p. 253, and
    erratum p. 5, book line 32: a positive
    atom at the base point cannot be omitted
    from a density-full agreement set. Prove the
    required exclusion directly from small masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MetricClosedBalls MetricDensities MetricDensityZeroPowerMass ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_zero_density_excludes_positive_atom]:
    the point-mass qualification in the erratum
    to Federer 3.2.16, p. 253 line 32.
    A zero-density exceptional set cannot contain
    a base point with positive atomic mass. *)
Theorem metric_zero_density_excludes_positive_atom (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A : set X) a :
  is_measure mu -> 0<mu [set a] ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0 -> ~ A a.
Proof.
move=> hm hAtom hA haA.
have hzero : mu [set a]<=0.
  apply: (@extended_real_reciprocal_upper_bound R (mu [set a]) 0%R)=> n.
  pose e : R := ((n.+1%:R : R)^-1)%R.
  have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
  have [d [hd hsmall]] := @metric_zero_density_small_power_mass R X m mu A a hm hA e he.
  pose r := (Num.min d 1/2)%R.
  have hmin : (0<Num.min d 1)%R by rewrite lt_min hd ltr01.
  have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
  have hhalf : (r<Num.min d 1)%R by rewrite /r; lra.
  have hmd : (Num.min d 1<=d)%R by rewrite ge_min lexx.
  have hm1 : (Num.min d 1<=1)%R by rewrite ge_min lexx orbT.
  have hrd : (r<=d)%R := le_trans (ltW hhalf) hmd.
  have hr1 : (r<=1)%R := le_trans (ltW hhalf) hm1.
  have hrad : (0<r<=d)%R by apply/andP; split.
  have hsmallr := hsmall r hrad.
  have hsub : [set a] `<=` A `&` metric_closed_ball a r.
    move=> x ->; split=> //; change (is_true (mdist a a<=r)%R).
    by rewrite mdistxx; exact: ltW hr.
  have hpoint := @measure_mono R X mu hm _ _ hsub.
  have hpow : (r^+m<=1)%R := exprn_ile1 m (ltW hr) hr1.
  have hcost : (e*r^+m<=e)%R by have hh:=ler_wpM2l (ltW he) hpow; rewrite mulr1 in hh.
  rewrite add0r; apply: le_trans hpoint (le_trans hsmallr _).
  by rewrite lee_fin.
by have := lt_le_trans hAtom hzero; rewrite ltxx.
Qed.
