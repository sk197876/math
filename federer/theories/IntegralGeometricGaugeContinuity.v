(** Federer (1969), 2.10.5, p. 172, last paragraph, paraphrased: for bounded
    Suslin S, beta_t zeta_t(S) is nondecreasing and continuous in t, and
    zeta_t(S) is continuous. The numerator facts follow from the proved
    scalar reduction and 2.4.17, p. 90. The quotient uses the separately
    proved continuity and strict positivity of the actual beta_t. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology normedtype realfun.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric SuslinSetUP
  RealMetricBackground ExtendedRealOrderTopology ExtendedArithmeticContinuity MeasurableRealEmbedding
  EuclideanProjectionMetric ProjectedVolumeMeasurability NonnegativeExtendedExponentNorm
  NonnegativeExtendedExponentNormUP OrthogonalProjectionProbability
  ProjectionBeta ProjectionBetaContinuity IntegralGeometricGauge BoundedProjectedVolumeNorm
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_normalized_gauge_monotone_bounded]:
    direct nondecreasing beta_t zeta_t(S) assertion
    for bounded Suslin S in Federer 2.10.5,
    p. 172, including equal exponents and infinity. *)
Theorem integral_geometric_normalized_gauge_monotone_bounded (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (s t : \bar R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S -> 1<=s -> s<=t ->
  (@projection_beta R n m hmn s)%:E * @integral_geometric_gauge R n m hmn s S <=
  (@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S.
Proof.
move=> hb hS hs hst; have ht := le_trans hs hst.
rewrite (@integral_geometric_gauge_normalized R n m hmn s hs S)
  (@integral_geometric_gauge_normalized R n m hmn t ht S).
exact: (@bounded_projected_volume_norm_monotone R n m hmn S c s t hb hS hs hst).
Qed.

(** Source for [integral_geometric_normalized_gauge_continuous_bounded]:
    direct numerator continuity in Federer 2.10.5,
    p. 172, on the full interval [1,infinity]. *)
Theorem integral_geometric_normalized_gauge_continuous_bounded (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S ->
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    (((@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S) :
      extended_real_line R)).
Proof.
move=> hb hS.
have hh := @bounded_projected_volume_norm_continuous R n m hmn S c hb hS.
apply: subspace_eq_continuous _ hh=> t ht.
have ht' : 1<=t by move: ht; rewrite inE.
exact: esym (@integral_geometric_gauge_normalized R n m hmn t ht' S).
Qed.

(** Source for [integral_geometric_gauge_continuous_bounded]:
    direct continuity of zeta_t(S) for bounded
    Suslin S in Federer 2.10.5, p. 172.
    The quotient is justified by the positive,
    continuous actual beta; the infinity endpoint
    is included in the exponent interval. *)
Theorem integral_geometric_gauge_continuous_bounded (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S ->
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    (@integral_geometric_gauge R n m hmn t S : extended_real_line R)).
Proof.
move=> hb hS.
pose T := subspace [set t : extended_real_line R | 1<=t].
pose b (t : T) : real_line_metric R := @projection_beta R n m hmn t.
pose f (t : T) : extended_real_line R := (b t)^-1%R%:E.
pose g (t : T) : extended_real_line R :=
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projected_volume_function (m:=m) S) t.
have hbc : continuous b := @projection_beta_real_continuous R n m hmn.
have hfc : continuous f.
  rewrite continuous_subspace_in=> t ht.
  have ht' : 1<=t by move: ht; rewrite inE.
  have hbn : b t!=0%R by rewrite gt_eqF //; exact: (@projection_beta_positive R n m hmn t ht').
  have hi := @continuousV R T b t hbn (hbc t).
  exact: continuous_comp hi (@real_extended_embedding_continuous R ((b t)^-1)%R).
have hgc : continuous g := @bounded_projected_volume_norm_continuous R n m hmn S c hb hS.
have hpair := topological_pair_continuous hfc hgc.
rewrite continuous_subspace_in=> t ht.
have ht' : 1<=t by move: ht; rewrite inE.
have hff : f t \is a fin_num by rewrite /f fin_numE.
have hgn : 0<=g t.
  have hn := @integral_geometric_gauge_norm_specification R n m hmn t ht' S hS.
  rewrite (@integral_geometric_gauge_normalized R n m hmn t ht' S) in hn.
  exact: nonnegative_extended_exponent_norm_nonnegative hn.
have hgf : g t \is a fin_num.
  rewrite (ge0_fin_numE hgn).
  exact: (@bounded_projected_volume_norm_finite R n m hmn S c t hb hS ht').
have hdef : mule_def (f t) (g t) := mule_def_fin hff hgf.
exact: continuous_comp (hpair t) (@extended_multiply_continuous_at_defined R (f t,g t) hdef).
Qed.
