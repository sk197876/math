(** Supporting closure gauge for the closed convex alternative in Federer
    (1969), 2.10.4(2), p. 172. An open convex set's closure lies in every
    strict homothetic enlargement about an interior point. Actual projected
    Lebesgue volumes scale polynomially; let the enlargement parameter
    approach one through strict upper bounds. The conclusion is restricted
    to open convex sets, rather than incorrectly asserted for arbitrary
    dense subsets. Source context and homothety references:
    ProjectedVolumeDilation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  ProjectedVolumeGauge ProjectedVolumeDilation AffineDilation RealDilationSlack
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_gauge_open_convex_closure]:
    supporting unchanged closure cost for open convex
    generators in Federer 2.10.4(2), p. 172.
    Empty generators and infinite gauge values are
    included; m<=n is the printed dimensional premise. *)
Theorem projected_volume_gauge_open_convex_closure (R : realType) (n m : nat)
    (U : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (m<=n)%N -> open U -> @is_inner_convex R (R_n R n) U ->
  projected_volume_gauge m (closure U)=projected_volume_gauge m U.
Proof.
move=> hmn ho hc.
case: (pselect (U !=set0))=> [[a ha]|hno]; last first.
  have hU0 : U=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hno; by exists x.
  by rewrite hU0 closure0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact: projected_volume_gauge_mono (@subset_closure _ U).
have hn := @projected_volume_gauge_nonnegative R n m U hmn.
case he: (projected_volume_gauge m U) hn=> [c| |] hn; last 2 first.
- exact: leey.
- by [].
rewrite leNgt; apply/negP=> hbad.
have [q [hcq hqcl]] := @extended_rationals_order_dense R c%:E
  (projected_volume_gauge m (closure U)) hbad.
have hcb : (c<ratr q)%R by move: hcq; rewrite lte_fin.
have [t [ht hcost]] := @real_positive_dilation_cost_slack R m c (ratr q) hcb.
have ht0 : (0<t)%R := lt_trans ltr01 ht.
have hsub := @open_convex_closure_dilation_cover R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) U a t ho hc ha ht.
have hh := le_trans (@projected_volume_gauge_mono R n m (closure U) _ hsub)
  (@projected_volume_gauge_dilation_bound R n m U a t).
rewrite he (ger0_norm (ltW ht0)) -EFinM in hh.
have hlt : ((t^+m*c)%:E<(ratr q : R)%:E)%E by rewrite lte_fin mulrC.
by have := lt_trans (le_lt_trans hh hlt) hqcl; rewrite ltxx.
Qed.
