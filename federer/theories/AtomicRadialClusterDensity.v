(** Federer (1969), 3.3.18, p. 301: actual radial
    atoms give infinite upper degree-one density in each retained ray. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric AtomicRadialClusterBudgets
  GeometricErrorBudget MeasureUP MeasureBasic MeasureRestriction MetricClosedBalls MetricDensities
  EuclideanBallVolume PositiveRadiusUnboundedValues PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [atomic_radial_cluster_upper_density_infinite]: the
    actual conical density spikes supporting the false converse
    in Federer 3.3.18, p. 301. For a fixed original unit direction,
    actual atoms of mass at least c*w_k at distance w_k squared
    give arbitrarily large normalized values at arbitrarily small
    ORIGINAL radii. Retaining every sufficiently late original
    cluster point in S suffices. No infinite density or limiting
    profile is assumed. *)
Theorem atomic_radial_cluster_upper_density_infinite (R:realType) n
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (v:inner_metric_space (@euclidean_inner_productP R n)) (c:R) (K:nat):
  is_measure mu ->inner_norm (@euclidean_inner_productP R n) v= 1%R ->(0<c)%R ->
  (forall k,(K<=k)%N ->(c*geometric_error_budget (1:R) k)%R%:E<=
    mu [set (geometric_error_budget (1:R) k)^+2 *:v]) ->
  (forall k,(K<=k)%N ->S ((geometric_error_budget (1:R) k)^+2 *:v)) ->
  upper_metric_density 1 (measure_restrict mu S) (0%R:inner_metric_space (@euclidean_inner_productP R n))=+oo.
Proof.
move=>hMu hUnit hc hAtomic hSource.
rewrite /upper_metric_density; apply:positive_radius_upper_infinite_from_spikes=>b d hd.
pose B:=(`|b|+1)%R.
have hB:(0<B)%R by rewrite /B; have:=normr_ge0 b; lra.
have hCD:(0<c/(2*B))%R by rewrite divr_gt0 ?mulr_gt0 // ltr0n.
pose e:=(Num.min 1 (Num.min d (c/(2*B))))%R.
have he:(0<e)%R by rewrite /e !lt_min ltr01 hd hCD.
have [J hJ]:=@atomic_radial_cluster_budget_small R e he.
pose k:=maxn K J.
have hK:(K<=k)%N by rewrite /k leq_max leqnn.
have hJk:(J<=k)%N by rewrite /k leq_max leqnn orbT.
pose w:=geometric_error_budget (1:R) k.
have hw:(0<w)%R:=geometric_error_budget_positive k (@ltr01 R).
have hSmall:(w<e)%R:=hJ k hJk.
have hE1:(e<= 1)%R by rewrite /e ge_min lexx.
have hEInner:(e<=Num.min d (c/(2*B)))%R by rewrite /e ge_min lexx orbT.
have hInnerD:(Num.min d (c/(2*B))<=d)%R by rewrite ge_min lexx.
have hED:(e<=d)%R:=le_trans hEInner hInnerD.
have hEC:(e<=c/(2*B))%R.
  apply:le_trans hEInner _; by rewrite ge_min lexx orbT.
have hW1:(w<= 1)%R:=ltW (lt_le_trans hSmall hE1).
have hWD:(w<d)%R:=lt_le_trans hSmall hED.
have hWC:(w<=c/(2*B))%R:=ltW (lt_le_trans hSmall hEC).
pose r:=(w^+2)%R.
have hr:(0<r)%R by rewrite /r exprn_gt0.
have hRW:(r<=w)%R.
  have h:=ler_wpM2r (ltW hw) hW1; by rewrite mul1r -expr2 in h.
have hRD:(r<d)%R:=le_lt_trans hRW hWD.
pose z:=(r *:v)%R.
have hNorm:inner_norm (@euclidean_inner_productP R n) z=r.
  rewrite /z inner_normZ (ger0_norm (ltW hr)) hUnit mulr1.
  by [].
have hBall:metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R n)) r z.
  change (is_true (mdist (0%R:inner_metric_space (@euclidean_inner_productP R n)) z<=r)%R).
  rewrite inner_metric_distanceE sub0r inner_normN hNorm; exact:lexx.
have hSub:[set z] `<=` S `&` metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R n)) r.
  move=>x ->; split; first exact:hSource k hK.
  exact:hBall.
have hMass:=le_trans (hAtomic k hK) (measure_mono hMu hSub).
have hDen:(0<2*r)%R by rewrite mulr_gt0 // ltr0n.
have hInverse:(0<=(2*r)%R%:E^-1)%E by rewrite inve_ge0 lee_fin; exact:ltW hDen.
have hScaled:=lee_wpmul2r hInverse hMass.
have hSpike:=@atomic_radial_cluster_spike_scalar R b c w hc hw hWC.
exists r; split; first by apply/andP; split.
have hSpikeE:(b%:E<=(c*w/(2*w^+2))%R%:E)%E by rewrite lee_fin.
apply:le_trans hSpikeE _.
rewrite /metric_ball_density euclidean_unit_ball_volume1 expr1.
rewrite inver (gt_eqF hDen).
rewrite inver (gt_eqF hDen) -EFinM in hScaled.
exact hScaled.
Qed.
