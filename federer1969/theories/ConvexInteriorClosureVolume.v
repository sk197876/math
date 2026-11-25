(** Federer (1969), 3.2.35, p. 272:
    closing an arbitrary convex source with an
    interior point preserves its Lebesgue volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex ConvexInteriorContraction
  AffineDilation EuclideanLebesgueDimensions ProjectedVolumeDilation RealDilationSlack ExtendedRealOrderTopology
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_interior_closure_volume]:
    supporting arbitrary-source closure reduction
    for Steiner's formula, Federer 3.2.35,
    p. 272. Every strict homothetic enlargement
    covers the closure and has its proved
    polynomial volume. Strict scalar cost slack
    proves the reverse mass inequality. The
    source need not be open, Borel or Suslin;
    infinite mass is also retained in this helper. *)
Theorem convex_interior_closure_volume (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) a:
  is_inner_convex S ->interior S a ->
  euclidean_lebesgue_measure n (closure S)=euclidean_lebesgue_measure n S.
Proof.
move=>hS ha.
have hm:=euclidean_lebesgue_is_measure R n.
apply/eqP; rewrite eq_le; apply/andP; split; last exact:(@measure_mono R _ (@euclidean_lebesgue_measure R n) hm S (closure S) (@subset_closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S)).
have hn:=measure_nonnegative hm S.
case he:(euclidean_lebesgue_measure n S) hn=>[c| |] hn; last 2 first.
- exact:leey.
- by [].
rewrite leNgt; apply/negP=>hBad.
have [q [hcq hqClosure]]:=@extended_rationals_order_dense R c%:E
  (euclidean_lebesgue_measure n (closure S)) hBad.
have hcb:(c<ratr q)%R by move:hcq; rewrite lte_fin.
have [t [ht hCost]]:=@real_positive_dilation_cost_slack R n c (ratr q) hcb.
have ht0:(0<t)%R:=lt_trans ltr01 ht.
have hSubset:=@convex_interior_closure_dilation_cover R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) S a t hS ha ht.
have hBound:=measure_mono hm hSubset.
rewrite euclidean_affine_dilation_volume he (ger0_norm (ltW ht0)) -EFinM in hBound.
have hStrict:((t^+n*c)%R%:E<(ratr q:R)%:E) by rewrite lte_fin mulrC.
by have :=lt_trans (le_lt_trans hBound hStrict) hqClosure; rewrite ltxx.
Qed.
