(** Federer (1969), 3.1.1, p. 210: the inverse-function theorem.
    The quantitative ball theorem supplies the neighbourhoods and the
    inverse Lipschitz estimate; general metric topology supplies the
    homeomorphism of the resulting subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneInverseBall
  NormLocalHomeomorphismUP MetricSubsetBackground MetricSubsetCorestriction
  MetricInverseBoundHomeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_inverse_function]: Federer 3.1.1,
    p. 210, the inverse-function theorem. A class-one function from a
    complete normed space, whose differential at a has a bounded linear
    inverse, maps a neighbourhood of a homeomorphically onto a
    neighbourhood of f(a). The inverse identities and boundedness specify
    the printed linear homeomorphism hypothesis. *)
Theorem norm_class_one_inverse_function (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A : X -> Prop) (f : X -> Y) (D : X -> Hom X Y)
    (a : X) (M : Hom Y X) :
  is_norm_class_one_field NX NY A f D -> A a ->
  norm_bounded_linear NY NX M ->
  (forall v, M (D a v) = v) -> (forall w, D a (M w) = w) ->
  is_norm_local_homeomorphism hNX hNY A f a.
Proof.
move=> hf ha hM hML hLM.
have [r [s [K [hr [hs [hK [hAr [hbound [hinj honto]]]]]]]]] :=
  @norm_class_one_inverse_ball R X Y NX NY hNX hNY hcomplete A f D a M hf ha hM hML hLM.
pose U : set (real_norm_metric_space hNX) := fun x => NX (x-a) <= r.
pose V : set (real_norm_metric_space hNY) := fun y => exists x, U x /\ f x=y.
exists U, V; split.
- exists r; split=> // h hh; rewrite /U addrAC subrr add0r; exact: ltW hh.
- split.
  + exists s; split=> // k hk; apply: honto.
    by rewrite addrAC subrr add0r; exact: ltW hk.
  + split; first exact hAr.
    have hFV : forall x : metric_subset U, V (f (val x)).
      by move=> x; exists (val x); split=> //; exact: set_valP x.
    pose F := @metric_subset_corestriction R [the metricType R of real_norm_metric_space hNY]
      (metric_subset U) V (fun x => f (val x)) hFV.
    exists F; split; first by move=> x.
    apply: (@metric_inverse_bound_homeomorphism R
      [the metricType R of metric_subset U] [the metricType R of metric_subset V] F K).
    * move=> x W hW.
      have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (F x) W) hW.
      have hxA := hAr (val x) (set_valP x).
      have [d [hd hc]] := (norm_class_one_zero hf hxA).2 e he.
      apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
      exists d=> // z hz; apply: hb.
      change (NY (f (val x)-f (val z)) < e).
      rewrite (real_seminorm_subtract hNY.1).
      have heq : val x+(val z-val x)=val z by rewrite addrC subrK.
      have hzA : A (val x+(val z-val x)) by rewrite heq; exact: hAr _ (set_valP z).
      have hsmall : NX (val z-val x) < d.
        rewrite (real_seminorm_subtract hNX.1); exact hz.
      have hh := hc (val z-val x) hzA hsmall; by rewrite heq in hh.
    * move=> x z heq; apply: val_inj; apply: hinj.
      - exact: set_valP x.
      - exact: set_valP z.
      - exact: (congr1 (fun y : metric_subset V => val y) heq).
    * move=> y; have [x [hx hfx]] := set_valP y.
      exists (@exist X (fun x => x \in U) x (mem_set hx)).
      apply: val_inj; exact hfx.
    * exact: ltW hK.
    * move=> x z; exact: hbound (val x) (val z) (set_valP x) (set_valP z).
Qed.
