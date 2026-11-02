(** Federer (1969), 3.2.35, p. 271:
    the closure of the original open convex
    body is exactly its closed unit gauge sublevel. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerConvex MinkowskiGaugeUP MinkowskiGaugeHomogeneity MinkowskiGaugeSublevel
  NormOpenConvexMinkowskiSublevel NormMinkowskiGaugeContinuity NormSmallStrictContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_convex_minkowski_closure]:
    supporting the boundary radial representation of
    Federer 3.2.35, p. 271. Actual
    continuity contains the closure in {g<=1}.
    Every point of {g<=1} is approached by
    strict radial contractions lying in the original
    S={g<1}. This proves the converse using
    neighbourhoods, without a closed-hull assumption. *)
Theorem norm_open_convex_minkowski_closure (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R):
  @is_minkowski_gauge R V S g ->
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->forall x:V,
  @closure [the topologicalType of real_norm_metric_space hN] S x <->g x<=1.
Proof.
move=>hG hOpen hConvex hZero x.
have [r [hr hRadius]]:=(@norm_domain_interior_neighbourhood R V N hN S 0).2
  (open_nbhs_nbhs (conj hOpen hZero)).
have hBall y:N y<r ->S y.
  move=>hy; have hh:=hRadius y hy; by rewrite add0r in hh.
have hClosed:=@norm_minkowski_gauge_closed_unit_sublevel R V N hN S g r hG hConvex hr hBall.
split.
- move=>hx.
  have hSubset:S `<=` [set y|g y<=1].
    move=>y hy.
    have hStrict:=(@norm_open_convex_minkowski_sublevel R V N hN S g hG hOpen hConvex hZero y).1 hy.
    exact:ltW hStrict.
  exact (hClosed x (@closureS [the topologicalType of real_norm_metric_space hN]
    S [set y|g y<=1] hSubset x hx)).
- move=>hx U hU.
  have [d [hd hRadiusU]]:=(@norm_domain_interior_neighbourhood R V N hN U x).2 hU.
  have [t [ht0 [ht1 hNear]]]:=@norm_small_strict_contraction R V N hN x d hd.
  have hBound:t*g x<=t.
    have hh:=ler_wpM2l (ltW ht0) hx; by rewrite mulr1 in hh.
  have hStrict:g (t*:x)<1.
    rewrite (@minkowski_gauge_positive_homogeneous R V S g hG t x ht0).
    exact:(le_lt_trans hBound ht1).
  exists (t*:x); split.
  + exact:(@minkowski_gauge_strict_sublevel_member R V S g (t*:x) hG hConvex hZero hStrict).
  + have hh:=hRadiusU (t*:x-x) hNear.
    by rewrite addrC subrK in hh.
Qed.
