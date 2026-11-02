(** Federer (1969), 3.2.31, p. 269: supporting local unit
    Lipschitz estimate after a small symmetric linear rescaling.
    A continuous actual differential field proves the neighborhood
    bound from the pointwise half-contraction. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric InnerNormedTopology HilbertFormCompactness RealNormUP NormClassOneUP NormClassOneLinearPostcompose
  NormFiniteLinearBound LinearRankAtLeast LipschitzUP MetricClosedBalls
  SmallExteriorMajorantUP SmallExteriorMajorantExistence ClassOneHalfDerivativeLocalContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_small_exterior_neighborhood]: supporting
    the restriction Lip(t^-1 f|E)<=1 in Federer 3.2.31,
    p. 269. The symmetric automorphism, its actual exterior norm,
    both inverse identities, and a positive closed-ball radius
    are all proved witnesses. No local Lipschitz bound or
    dimensional comparison is assumed. *)
Theorem class_one_small_exterior_neighborhood (R:realType) m v mu
    (G:R_n R m->R_n R v) (D:R_n R m->Hom (R_n R m) (R_n R v))
    (a:inner_metric_space (@euclidean_inner_productP R m)) (epsilon:R):
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT G D ->
  ~linear_rank_at_least (D a) mu ->0<epsilon ->
  exists T U r,@is_small_exterior_majorant R m v mu (D a) epsilon T U /\0<r /\
    @is_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R v))
      (metric_closed_ball a r) (fun x=>U (G x)) 1.
Proof.
move=>hG hRank heps.
have [T [U hMajor]]:=@small_exterior_majorant_exists R m v mu (D a) epsilon hRank heps.
have hNM:=inner_norm_real_norm (@euclidean_inner_productP R m).
have hNV:=inner_norm_real_norm (@euclidean_inner_productP R v).
have hU:=@norm_finite_linear_bounded R (R_n R v) (R_n R v)
  (inner_norm (@euclidean_inner_productP R v)) (inner_norm (@euclidean_inner_productP R v))
  hNV hNV v (@coordinate_basis R v) (@coordinate_basisP R v) U.
have hPost:=@norm_class_one_linear_postcompose R (R_n R m) (R_n R v) (R_n R v)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R v))
  (inner_norm (@euclidean_inner_productP R v)) hNM hNV setT G D U hG hU.
have hPoint x:inner_norm (@euclidean_inner_productP R v) (hom_comp U (D a) x)<=
    (1/2)*inner_norm (@euclidean_inner_productP R m) x.
  exact (@small_exterior_majorant_contraction R m v mu (D a) epsilon T U hMajor x).
have [d [hd hLocal]]:=@class_one_half_derivative_local_contraction R (R_n R m) (R_n R v)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R v))
  hNM hNV (fun x=>U (G x)) (fun x=>hom_comp U (D x)) a hPost hPoint.
pose r:=d/2.
have hTwo:0<(2:R) by rewrite ltr0n.
have hr:0<r by rewrite /r divr_gt0.
have hrd:r<d.
  by rewrite /r (@ltr_pdivrMr R 2 d d hTwo) -[ltLHS]mulr1 (ltr_pM2l hd) ltr1n.
exists T,U,r; split; first exact hMajor.
split=>//; split; first exact:ler01.
move=>x y hx hy; rewrite mul1r !inner_metric_distanceE.
apply:hLocal.
- apply:le_lt_trans _ hrd.
  by move:hx; rewrite /metric_closed_ball /= inner_metric_distanceE -[a-x]opprB inner_normN.
- apply:le_lt_trans _ hrd.
  by move:hy; rewrite /metric_closed_ball /= inner_metric_distanceE -[a-y]opprB inner_normN.
Qed.
