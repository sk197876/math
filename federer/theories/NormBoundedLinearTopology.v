(** Federer (1969), 3.1.1, p. 209: the norm-ball and finite-bound laws
    express exactly the printed interior and continuity hypotheses.
    Only general metric topology is imported; no differentiation theorem
    or finite-dimensional assumption is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormMetricScaleContinuity
  NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_domain_interior_neighbourhood]: supporting exact
    interpretation of a in Int A in Federer 3.1.1, p. 209. The domain
    contains an open norm ball exactly when it is a neighbourhood of a. *)
Lemma norm_domain_interior_neighbourhood (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (A : set X) (a : X) :
  norm_domain_interior NX A a <-> nbhs (a : real_norm_metric_space hNX) A.
Proof.
split.
- move=> [r [hr hA]].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a : real_norm_metric_space hNX) A)).
  exists r=> // x hx.
  have hh : NX (x-a) < r.
    rewrite (real_seminorm_subtract hNX.1); exact hx.
  have h := hA (x-a) hh; by rewrite addrC subrK in h.
- move=> ha.
  have [r hr hA] := proj1 (metricType_numDomainType.nbhs_mdistP (a : real_norm_metric_space hNX) A) ha.
  exists r; split=> // h hh; apply: hA.
  change (NX (a-(a+h)) < r).
  by rewrite opprD addrA subrr add0r (real_seminorm_negate hNX.1).
Qed.

(** Source for [norm_bounded_linear_continuous]: supporting direction of
    the continuous-linear requirement in Federer 3.1.1, p. 209: a finite
    norm bound implies continuity in the supplied norm topologies. *)
Lemma norm_bounded_linear_continuous (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) :
  norm_bounded_linear NX NY L ->
  continuous (fun x : real_norm_metric_space hNX =>
    (L x : real_norm_metric_space hNY)).
Proof.
move=> [C [hC hL]].
apply: (@metric_fixed_lipschitz_continuous R _ _ _ C hC).
move=> x y; change (NY (L x-L y) <= C * NX (x-y)).
by rewrite -linearB; exact: hL.
Qed.

(** Source for [norm_continuous_linear_bounded]: supporting converse of
    the continuous-linear requirement in Federer 3.1.1, p. 209.
    Continuity at zero and homogeneity supply a finite bound, without
    compactness of a unit sphere or finite dimension. *)
Lemma norm_continuous_linear_bounded (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) :
  continuous (fun x : real_norm_metric_space hNX =>
    (L x : real_norm_metric_space hNY)) -> norm_bounded_linear NX NY L.
Proof.
move=> hL.
have hball : nbhs (L (0:X) : real_norm_metric_space hNY)
    [set z | mdist (L 0 : real_norm_metric_space hNY) z < 1].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (L (0:X) : real_norm_metric_space hNY) _)).
  exists 1; first exact: ltr01.
  by move=> z hz.
have hpre := hL (0 : real_norm_metric_space hNX) _ hball.
have [d hd hdelta] := proj1
  (metricType_numDomainType.nbhs_mdistP (0 : real_norm_metric_space hNX) _) hpre.
have hC : 0 < 2/d by rewrite divr_gt0 // ltr0n.
exists (2/d); split; first exact: ltW hC.
move=> x; have [->|hx] := eqVneq x 0.
  by rewrite linear0 (real_seminorm_zero hNY.1) (real_seminorm_zero hNX.1) mulr0.
have hnx : 0 < NX x by rewrite (real_norm_positive hNX.1 hNX.2).
pose t := d/(2*NX x).
have ht : 0 < t by rewrite /t divr_gt0 // mulr_gt0 // ltr0n.
have htx : NX (t *: x) = d/2.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) /t invfM mulrA.
  by rewrite divfK // gt_eqF.
have hsmall : mdist (0 : real_norm_metric_space hNX) (t *: x) < d.
  change (NX (0-t *: x) < d).
  rewrite sub0r (real_seminorm_negate hNX.1) htx.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hb := hdelta (t *: x) hsmall.
change (is_true (NY (L 0-L (t *: x)) < 1)) in hb.
rewrite linear0 sub0r (real_seminorm_negate hNY.1) linearZ /=
  (real_seminorm_scale hNY.1) (ger0_norm (ltW ht)) in hb.
have hbound : NY (L x) < t^-1 by rewrite -div1r ltr_pdivlMr // mulrC.
apply: ltW; apply: lt_le_trans hbound _.
by rewrite /t invf_div mulrAC.
Qed.
