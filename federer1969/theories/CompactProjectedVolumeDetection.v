(** Federer (1969), 3.2.37, p. 274: compact source sets
    detect strict lower bounds for a Borel piece's projected-volume
    gauge. The supporting assertion allows every Suslin source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions EuclideanSuslinCompactImageBound ProjectedVolumeGauge
  SuslinSetUP CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_gauge_compact_detection]: the
    compact detection step in the finite-family supremum cited in
    Federer 3.2.37, p. 274. Compactness holds in the original
    source and every projection is actual; no measurable selection
    or finiteness premise is assumed. *)
Theorem projected_volume_gauge_compact_detection (R:realType) n m
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (b:R):
  is_suslin_set R S -> b%:E<projected_volume_gauge m S ->
  exists (K:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:{linear R_n R n->R_n R m}),
    [/\ compact K,K `<=` S,O_star p & b%:E<@euclidean_lebesgue_measure R m (p @` K)].
Proof.
move=>hS hLarge; apply:contrapT=>hNo.
have hBound:projected_volume_gauge m S<=b%:E.
  apply:projected_volume_gauge_least_bound=>p hp.
  have [q hq]:=euclidean_projection_linear_complete hp.
  have hEqual:(p:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R m))=euclidean_projection_linear q.
    apply:funext=>x; exact:esym (hq x).
  have hCont:continuous (p:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R m)).
    rewrite hEqual; exact:euclidean_projection_continuous.
  have hCompact:forall K,compact K ->K `<=` S ->
      @euclidean_lebesgue_measure R m (p @` K)<=b%:E.
    move=>K hK hKS; rewrite leNgt; apply/negP=>hCost.
    apply:hNo; exists K,p; by split.
  exact (@euclidean_suslin_compact_image_mass_bound R
    (inner_metric_space (@euclidean_inner_productP R n)) m p S b
    (@euclidean_metric_complete R n) (@euclidean_metric_separable R n) hCont hS hCompact).

have hBad:=lt_le_trans hLarge hBound; by rewrite ltxx in hBad.
Qed.
