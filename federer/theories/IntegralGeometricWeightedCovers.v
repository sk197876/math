(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting
    weighted-cover estimate for the actual normalized integral-geometric
    gauge of 2.10.5(1), pp. 172–173. Integrate the projected characteristic
    sums, use nonnegative extended-input norm homogeneity and the countable
    triangle bound of 2.4.12, pp. 86–87, then divide by beta. This is an
    intermediate estimate, not the final weighted-integral equality. no
    identical geometric theorem is attributed to them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  ProjectedVolumeMeasurability ProjectedVolumeWeightedCovers OrthogonalProjectionProbability
  ProjectionBeta IntegralGeometricGauge NonnegativeExtendedExponentNorm NonnegativeExtendedNormScale
  ProbabilityExtendedNormCover PartialFunctionBasic MeasurableFunctionUP MeasureUP
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale WeightedMetricEnvelopeUP TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_weighted_cover]: supporting
    fractional-cover estimate for the integral-geometric
    application in 2.10.24, p. 188. Countable indexed
    Borel families may have repeated members, infinite
    projected volumes and infinite total cost. Finite
    nonnegative weights, every exponent at least one,
    and zero thresholds are allowed. This does not
    assert the final weighted-integral equality. *)
Theorem integral_geometric_gauge_weighted_cover (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : \bar R) (J : choiceType)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (G : set J) (u : J -> R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  1<=p -> countable G -> (forall j, G j -> (0<=u j)%R) -> borel_set A ->
  (forall j, G j -> borel_set (S j)) -> (0<=r)%R ->
  (forall x, A x -> r%:E<=weighted_generator_sum S G u x) ->
  r%:E*@integral_geometric_gauge R n m hmn p A<=
    nonnegative_sum G (fun j=>(u j)%:E*@integral_geometric_gauge R n m hmn p (S j)).
Proof.
move=> hp hG hu hA hS hr hdom.
have hrE : 0<=r%:E by rewrite lee_fin.
have huE j (hj : G j) : 0<=(u j)%:E by rewrite lee_fin; exact: hu.
pose mu := @orthogonal_projection_probability R n m hmn.
have hm : is_measure mu := @theta_star_is_measure R n m hmn.
pose v j := if j \in G then u j else 0%R.
have hv j : (0<=v j)%R.
  rewrite /v; case: ifPn=> // hj; exact: hu (set_mem hj).
have hvE j : 0<=(v j)%:E by rewrite lee_fin; exact: hv.
have hvu j (hj : G j) : v j=u j by rewrite /v mem_set //.
have hFA := @theta_star_projected_volume_measurable R n m hmn A (metric_borel_suslin hA).
have hFS j (hj : G j) := @theta_star_projected_volume_measurable R n m hmn (S j)
  (metric_borel_suslin (hS j hj)).
have hvol q : r%:E*projected_volume_function (m:=m) A q<=
    nonnegative_sum G (fun j=>(v j)%:E*projected_volume_function (m:=m) (S j) q).
  have hh := @projection_weighted_cover_threshold R n m J S G u A q r hG hu hA hS hr hdom.
  have he : nonnegative_sum G (fun j=>(v j)%:E*projected_volume_function (m:=m) (S j) q)=
      nonnegative_sum G (fun j=>(u j)%:E*projected_volume_function (m:=m) (S j) q).
    by apply: nonnegative_sum_ext=> j hj; rewrite hvu.
  by rewrite he.
have hnorm := @probability_nonnegative_extended_norm_cover R _ J mu hm p G
  (fun q=>r%:E*projected_volume_function (m:=m) A q)
  (fun j q=>(v j)%:E*projected_volume_function (m:=m) (S j) q)
  (@theta_star_total R n m hmn) hG hp
  (fun q=>mule_ge0 hrE (projected_volume_function_nonnegative A q))
  (fun j q=>mule_ge0 (hvE j) (projected_volume_function_nonnegative (S j) q))
  (@measurable_total_extended_scale R _ mu hm _ r hFA)
  (fun j hj=>@measurable_total_extended_scale R _ mu hm _ (v j) (hFS j hj)) hvol.
rewrite (@nonnegative_extended_norm_scale R _ mu hm (projected_volume_function (m:=m) A)
  p r (fun q=>projected_volume_function_nonnegative A q) hp hr hFA) in hnorm.
have he : nonnegative_sum G (fun j=>nonnegative_extended_exponent_norm mu
      (fun q=>(v j)%:E*projected_volume_function (m:=m) (S j) q) p)=
    nonnegative_sum G (fun j=>(u j)%:E*nonnegative_extended_exponent_norm mu
      (projected_volume_function (m:=m) (S j)) p).
  apply: nonnegative_sum_ext=> j hj.
  by rewrite (@nonnegative_extended_norm_scale R _ mu hm (projected_volume_function (m:=m) (S j))
    p (v j) (fun q=>projected_volume_function_nonnegative (S j) q) hp (hv j) (hFS j hj)) hvu.
rewrite he in hnorm.
pose b := (@projection_beta R n m hmn p)^-1%R.
have hb : (0<=b)%R.
  rewrite /b invr_ge0; exact: ltW (@projection_beta_positive R n m hmn p hp).
have hnorm0 j (hj : G j) : 0<=nonnegative_extended_exponent_norm mu
    (projected_volume_function (m:=m) (S j)) p.
  exact: (@nonnegative_extended_exponent_norm_ge0 R _ mu _ p hm
    (fun q=>projected_volume_function_nonnegative (S j) q) hp (hFS j hj)).
have hcost : nonnegative_sum G (fun j=>(u j)%:E*(b%:E*
      nonnegative_extended_exponent_norm mu (projected_volume_function (m:=m) (S j)) p))=
    b%:E*nonnegative_sum G (fun j=>(u j)%:E*
      nonnegative_extended_exponent_norm mu (projected_volume_function (m:=m) (S j)) p).
  rewrite -nonnegative_sum_scale //; last by move=> j hj; exact: mule_ge0 (huE j hj) (hnorm0 j hj).
  apply: nonnegative_sum_ext=> j hj; by rewrite !muleA [(u j)%:E*b%:E]muleC.
rewrite /integral_geometric_gauge -/mu -/b hcost.
rewrite muleA [r%:E*b%:E]muleC -muleA.
apply: lee_wpmul2l hnorm; exact hb.
Qed.
