(** Federer (1969), 3.1.24, p. 238: the
    common ball on which every positive-degree coefficient has
    norm at most one. These supporting lemmas separate the
    finitely many early coefficients from the uniform-series tail. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_homogeneous_polynomial_zero]: supporting
    the radius choice in Federer 3.1.24, p. 238.
    A positive-degree homogeneous polynomial vanishes at zero,
    by its scaling law with scalar zero. *)
Lemma positive_homogeneous_polynomial_zero (R:realType) (X Y:lmodType R)
    m (P:X->Y) : (0<m)%N -> @is_homogeneous_polynomial R X Y m P -> P 0=0.
Proof.
case:m=>[|m] hm [phi hphi]; first by [].
have hh:=sform_polynomial_scale_argument phi (0:R) (0:X).
rewrite scale0r expr0n scale0r in hh.
by rewrite hphi hh.
Qed.

(** Source for [norm_continuous_zero_local_bound]: supporting
    the same radius choice, Federer 3.1.24, p. 238.
    Continuity at zero gives a small ball with output norm
    less than any prescribed positive bound. *)
Lemma norm_continuous_zero_local_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (P:X->Y) e :
  P 0=0 ->
  continuous (fun x:real_norm_metric_space hNX=>(P x:real_norm_metric_space hNY)) ->
  0<e -> exists r:R,0<r /\ forall v,NX v<r -> NY (P v)<e.
Proof.
move=>h0 hc he.
have hb:nbhs (P 0:real_norm_metric_space hNY)
    [set y|mdist (P 0:real_norm_metric_space hNY) y<e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (P 0:real_norm_metric_space hNY) _)).
  exists e=>//; by move=>y hy.
have [r hr hh]:=proj1 (metricType_numDomainType.nbhs_mdistP (0:real_norm_metric_space hNX) _)
  (hc (0:real_norm_metric_space hNX) _ hb).
exists r; split; first exact hr.
move=>v hv.
have hd:mdist (0:real_norm_metric_space hNX) v<r.
  change (NX (0-v)<r); by rewrite sub0r (real_seminorm_negate hNX.1).
have hp:=hh v hd.
change (is_true (NY (P 0-P v)<e)) in hp.
by rewrite h0 sub0r (real_seminorm_negate hNY.1) in hp.
Qed.

(** Source for [norm_finite_polynomial_coefficients_ball]: supporting
    the beginning of (4) to (1), Federer 3.1.24,
    p. 238. A finite family of positive-degree continuous
    homogeneous coefficients is bounded by one on a common ball. *)
Lemma norm_finite_polynomial_coefficients_ball (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (P:nat->X->Y) n :
  (forall m,@is_homogeneous_polynomial R X Y m (P m) /\
    continuous (fun x:real_norm_metric_space hNX=>(P m x:real_norm_metric_space hNY))) ->
  exists r:R,0<r /\ forall m,(0<m<=n)%N -> forall v,NX v<r -> NY (P m v)<=1.
Proof.
move=>hP; elim:n=>[|n [r [hr hh]]].
- exists 1; split; first exact ltr01.
  by move=>[|m].
- have h0:=positive_homogeneous_polynomial_zero (ltn0Sn n) (hP n.+1).1.
  have [d [hd hb]]:=@norm_continuous_zero_local_bound R X Y NX NY hNX hNY
    (P n.+1) 1 h0 (hP n.+1).2 ltr01.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  move=>m /andP [hm0 hmn] v; rewrite lt_min=>/andP [hvr hvd].
  move:hmn; rewrite leq_eqVlt=>/orP [/eqP ->|hmlt].
    exact: ltW (hb v hvd).
  have hm:(0<m<=n)%N by rewrite hm0 -ltnS.
  exact (hh m hm v hvr).
Qed.
