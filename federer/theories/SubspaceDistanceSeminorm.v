(** Supporting normed-space background for the separability reduction in
    Federer (1969), 2.9.22, p. 167: distance to a vector subspace is a
    seminorm. This is used with Hahn–Banach to separate a point from a
    closed subspace; it is not separately stated in 2.9.22. The proof uses
    only the abstract distance infimum laws of 2.2.10, p. 66, and the
    seminorm laws of 2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import ModuleQuotient RealNormUP NormMetric
  MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section DistanceSeminorm.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable Z : subspace E.
Variable d : E -> R.
Hypothesis hd : is_metric_set_distance (fun y : real_norm_metric_space hN => Z y) d.

(** Source for [subspace_distance_scale_bound]: supporting
    distance homogeneity for the closed-subspace separation used
    in Federer 2.9.22, p. 167. Apply the infimum laws
    after scaling points of the subspace. *)
Lemma subspace_distance_scale_bound (c : R) (x : E) : d (c *: x)<=`|c| * d x.
Proof.
case: (eqVneq c 0)=> [->|hc].
  rewrite scale0r normr0 mul0r.
  by rewrite (metric_set_distance_member hd (subspace_zero Z)).
have hp : 0<`|c| by rewrite normr_gt0.
have hdiv : d (c *: x)/`|c|<=d x.
  apply: (metric_set_distance_greatest hd)=> a ha.
  rewrite ler_pdivrMr //.
  have hh := metric_set_distance_lower hd (c *: x) (subspace_scale c ha).
  change (is_true (d (c *: x)<=N (c *: x-c *: a))) in hh.
  rewrite -scalerBr (real_seminorm_scale hN.1) in hh.
  by rewrite mulrC.
by move: hdiv; rewrite ler_pdivrMr // mulrC.
Qed.

(** Source for [subspace_distance_is_seminorm]: supporting
    quotient seminorm for the closed-subspace arguments in Federer
    2.9.22, p. 167. The triangle estimate takes the two
    infima through their greatest-lower-bound laws; no choice of
    nearest points or inner product is assumed. *)
Theorem subspace_distance_is_seminorm : is_real_seminorm d.
Proof.
constructor.
- exact: metric_set_distance_nonnegative hd.
- move=> c x; case: (eqVneq c 0)=> [->|hc].
    rewrite scale0r normr0 mul0r.
    exact (@metric_set_distance_member R
      [the metricType R of real_norm_metric_space hN] _ d hd 0 (subspace_zero Z)).
  apply/le_anti/andP; split; first exact: subspace_distance_scale_bound.
  have hh := subspace_distance_scale_bound c^-1 (c *: x).
  rewrite scalerA mulVf // scale1r normfV mulrC in hh.
  have hp : 0<`|c| by rewrite normr_gt0.
  by move: hh; rewrite ler_pdivlMr // mulrC.
- move=> x y.
  have hfirst a : Z a -> d (x+y)<=N (x-a)+d y.
    move=> ha.
    have hb : d (x+y)-N (x-a)<=d y.
      apply: (metric_set_distance_greatest hd)=> b hb.
      have hh := metric_set_distance_lower hd (x+y) (subspace_add ha hb).
      change (is_true (d (x+y)<=N ((x+y)-(a+b)))) in hh.
      have hid : (x+y)-(a+b)=(x-a)+(y-b).
        by rewrite opprD addrACA.
      rewrite hid in hh.
      have ht := real_seminorm_triangle hN.1 (x-a) (y-b).
      change (d (x+y)-N (x-a)<=N (y-b)).
      lra.
    lra.
  have hh : d (x+y)-d y<=d x.
    apply: (metric_set_distance_greatest hd)=> a ha.
    change (d (x+y)-d y<=N (x-a)).
    have ht := hfirst a ha; lra.
  lra.
Qed.

End DistanceSeminorm.
