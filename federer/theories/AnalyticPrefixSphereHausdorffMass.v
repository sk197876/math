(** Federer (1969), 3.4.8(6), p. 328:
    the original prefix sphere has the positive
    finite Hausdorff mass of the unit sphere
    in R^p. Exact original coordinates and
    the project covering theorem prove the identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct AnalyticPrefixCoordinatesUP
  AnalyticPrefixCoordinateLaws AnalyticPrefixSphereCoordinates AnalyticPrefixSphereAction
  MetricSubsetBackground HausdorffMetricSubset HausdorffMeasure HausdorffIsometricEmbedding
  HausdorffUnitSphereMass SphereGammaMass EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_sphere_hausdorff_mass]: the
    actual finite positive sphere mass needed to
    compare V_#mu_p with H^(p-1) restricted to S,
    3.4.8(6), p. 328. The normalization is
    the project's original Gamma normalization. *)
Theorem analytic_prefix_sphere_hausdorff_mass (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  p (hPN:(p<=n)%N) (P:Hom X (R_n R p)) (S:Hom (R_n R p) X)
  (hP:is_analytic_prefix_projection omega hPN P) (hS:is_analytic_prefix_section e hPN S)
  (hPositive:(0<p)%N):
  @hausdorff_measure R [the metricType R of metric_subset (@analytic_prefix_unit_sphere R X B hB n e p)]
    (p-1) setT = (2*(euler_gamma_half R)^+p/euler_gamma (@positive_dimension_half R p hPositive))%:E.
Proof.
pose XT:=inner_metric_space hB.
pose YT:=inner_metric_space (@euclidean_inner_productP R p).
pose sphere:=@analytic_prefix_unit_sphere R X B hB n e p.
have hCoordinates:=@analytic_prefix_sphere_image R X B hB n e he hON omega hDual p hPN P S hP hS.
have hLeft:cancel S P:=@analytic_prefix_projection_section R X n e omega p hPN P S hDual hP hS.
have hDistance (x y:YT):mdist (S x:XT) (S y:XT) = mdist x y.
  rewrite !inner_metric_distanceE.
  change (inner_norm hB (S x-S y) = inner_norm (@euclidean_inner_productP R p) (x-y)).
  have hLinear:S (x-y) = S x-S y:=linearB (hom_as_linear S) x y.
  rewrite -hLinear.
  exact:(@analytic_prefix_section_norm R X B hB n e hON p hPN S hS (x-y)).
have hMass:=@hausdorff_isometric_embedding_invariance R YT XT S P hLeft hDistance (p-1)
  [set y:YT|inner_norm (@euclidean_inner_productP R p) y = 1].
rewrite -(@hausdorff_metric_subset_measure R XT sphere (p-1) setT).
have hWhole:(fun u:metric_subset sphere=>(val u:XT)) @` setT = sphere.
  apply/seteqP;split=>x.
  - move=>[u _ <-];exact:set_valP.
  - move=>hX;exists (exist _ x (mem_set hX));by [].
rewrite hWhole /sphere -hCoordinates hMass.
exact:(@hausdorff_unit_sphere_gamma_mass R p hPositive).
Qed.
