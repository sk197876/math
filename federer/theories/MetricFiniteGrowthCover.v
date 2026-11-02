(** Federer (1969), 3.1.9, p. 218: every point with
    finite ordinary upper growth belongs to a uniform closed-center
    set. The upper limit is the existing punctured-neighborhood
    infimum of suprema, including extended values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds ExtendedRealOrderTopology
  ExtendedRealReciprocalBounds RealLatticeTruncationLimits
  MetricSlopeLimsup MetricLocalLipschitzCenters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [finite_metric_slope_local_bound]: supporting
    conversion of the limsup hypothesis in Federer 3.1.9,
    p. 218, into a positive finite coefficient and radius.
    No value is assigned at the omitted center of the quotient. *)
Lemma finite_metric_slope_local_bound (R : realType) (X Y : metricType R)
    (B : set X) (f : X->Y) a :
  (metric_local_slope_limsup B f a< +oo)%E ->
  exists M d : R, 0<M /\ 0<d /\ forall x, B x ->
    mdist a x<d -> mdist (f x) (f a)<=M*mdist x a.
Proof.
move=> hfin.
have [q [hq _]] := @extended_rationals_order_dense R
  (metric_local_slope_limsup B f a) +oo%E hfin.
pose M := `|ratr q : R|+1.
have hplus : `|ratr q : R|<M by rewrite /M ltrDl ltr01.
have hM : 0<M := le_lt_trans (normr_ge0 _) hplus.
have hqM : (ratr q : R)<M.
  apply: le_lt_trans (ler_norm _) _; by rewrite /M ltrDl ltr01.
have hlim : (metric_local_slope_limsup B f a<M%:E)%E.
  apply: lt_trans hq _; by rewrite lte_fin.
have [d [hd hs]] := metric_slope_limsup_radius hlim.
exists M,d; split=> //; split=> // x hx hdx.
case: (eqVneq a x)=> [->|hne]; first by rewrite !mdistxx mulr0.
have hp : 0<mdist a x by rewrite mdist_gt0.
have hval : ((mdist (f a) (f x)/mdist a x)%:E<=
    metric_slope_neighborhood_sup B f a d)%E.
  apply: extended_real_sup_upper; exists x; split=> //; split=> //.
  by apply/andP; split.
have hh := ltW (le_lt_trans hval hs).
rewrite lee_fin (ler_pdivrMr _ _ hp) in hh.
by rewrite (metric_sym (f x) (f a)) (metric_sym x a).
Qed.

(** Source for [finite_metric_slope_natural_center]: the
    inclusion of A in the union of C_j in Federer 3.1.9,
    p. 218. Openness supplies the whole neighborhood in B;
    increasing j simultaneously raises the coefficient and decreases
    the radius. Index j=0 represents the printed positive integer 1. *)
Theorem finite_metric_slope_natural_center (R : realType) (X Y : metricType R)
    (B : set X) (f : X->Y) a :
  open B -> B a -> (metric_local_slope_limsup B f a< +oo)%E ->
  exists j : nat, metric_local_lipschitz_centers B f
    (j.+1%:R) ((j.+1%:R)^-1) a.
Proof.
move=> hB ha hfin.
have hminl (x y : R) : Num.min x y<=x by rewrite ge_min lexx.
have hminr (x y : R) : Num.min x y<=y by rewrite ge_min lexx orbT.
have [M [d [hM [hd hbound]]]] := finite_metric_slope_local_bound hfin.
have hnb : nbhs a B by rewrite openE in hB; exact: hB a ha.
have [b hb hball] := (metricType_numDomainType.nbhs_mdistP a _).1 hnb.
have hsmall : 0<Num.min b d by rewrite lt_min hb hd.
have [p hp] := positive_reciprocal_nat_small hsmall.
pose N := Num.bound M.
pose j := maxn N p.
have hMj : M<j.+1%:R.
  apply: lt_le_trans (archi_boundP (ltW hM)) _.
  rewrite ler_nat; exact: leq_trans (leq_maxl N p) (leqnSn j).
have hr : (j.+1%:R : R)^-1<Num.min b d.
  exact: le_lt_trans (@positive_reciprocal_nat_antitone R p j (leq_maxr N p)) hp.
exists j; split=> // x hx.
have hxb : mdist a x<b := lt_le_trans (lt_trans hx hr) (hminl _ _).
have hxd : mdist a x<d := lt_le_trans (lt_trans hx hr) (hminr _ _).
have hxB := hball x hxb; split=> //.
apply: le_trans (hbound x hxB hxd) _.
apply: ler_wpM2r; [exact: mdist_ge0|exact: ltW hMj].
Qed.
