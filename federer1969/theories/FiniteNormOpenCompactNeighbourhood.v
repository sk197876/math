(** Federer (1969), 3.4.8(10), p. 332:
    a sufficiently small closed prefix ball
    lies in Y outside delta=0.
    Apply the existing finite-dimensional compact-ball
    theorem and the original open-domain laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric LinearBasis NormDifferentialUP
  NormBoundedLinearTopology FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_open_compact_neighbourhood]:
    the compact prefix neighbourhood used in
    the D_e argument, 3.4.8(10),
    p. 332. Its closed half-radius
    ball is a genuine neighbourhood and
    stays inside the given original open set. *)
Theorem finite_norm_open_compact_neighbourhood (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) d (e:'I_d->Y) (he:is_basis e)
    (V:set Y) (a:Y):
  @open (real_norm_metric_space hNY) V ->V a ->
  exists C:set Y,nbhs (a:real_norm_metric_space hNY) C /\
    compact [set y:real_norm_metric_space hNY|C y] /\C `<=` V.
Proof.
move=>hOpen ha.
have hNear:nbhs (a:real_norm_metric_space hNY) V by rewrite openE in hOpen;exact:hOpen a ha.
have [r [hR hLocal]]:=(@norm_domain_interior_neighbourhood R Y NY hNY V a).2 hNear.
pose C:set Y:=fun y=>NY (y-a)<=r/2.
have hHalf:0<r/2 by rewrite divr_gt0 // ltr0n.
have hSmaller:r/2<r by lra.
exists C;split.
- apply/(metricType_numDomainType.nbhs_mdistP (a:real_norm_metric_space hNY)).
  exists (r/2);first exact:hHalf.
  move=>y hy;change (is_true (NY (a-y)<r/2)) in hy.
  rewrite (real_seminorm_subtract hNY.1) in hy;exact:ltW hy.
split.
- exact:(@finite_norm_closed_ball_compact R Y d e he NY hNY a (r/2)).
- move=>y hy.
  have hSmall:NY (y-a)<r:=le_lt_trans hy hSmaller.
  have h:=hLocal (y-a) hSmall.
  by rewrite addrC subrK in h.
Qed.
