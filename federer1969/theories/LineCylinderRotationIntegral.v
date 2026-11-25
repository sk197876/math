(** Supporting Federer (1969), 2.10.46, p. 204: the inner rotation average
    in Freilich (1950), Theorem 4.5, Part 7, pp. 249–250. Fix a
    nonexceptional projection, choose its transverse factor once, and
    average over rotations of the second set. Finite I_1 measure makes the
    transverse projection integrals finite almost everywhere. This avoids a
    measurable selection of transverse factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm Hom
  RealMetricBackground EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalInjectionSpaces OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupSealed CompactGroupHaarNormalisation OrthogonalProbabilityBackground
  LineCylinderProjectionFactor ProjectionMultiplicityIntegral ProjectionMultiplicitySourceChange
  ProjectionOrbitMultiplicity FiniteProjectionOrbit IntegralGeometricMeasure ProjectionBeta
  LebesgueScalarMeasure TopologicalBorel ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality TotalNonnegativeExtendedScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CylinderRotation.
Variable R : realType.
Variables n k : nat.
Hypothesis hkn : (k<=n)%N.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation X := (inner_metric_space (@euclidean_inner_productP R n)).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n)) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.

(** Source for [line_cylinder_rotation_integral]: supporting
    inner integral in Freilich (1950), Theorem 4.5,
    Part 7, pp. 249–250, for 2.10.46, p. 204.
    The fixed projection's axis coefficient multiplies scalar
    length and beta_1 times I_1 of the second factor.
    This is a finite-factor cylinder step, not yet the full
    product identity or its normalization. *)
Theorem line_cylinder_rotation_integral
    (F : orthogonal_projection_metric_space R (1+n) (1+k))
    (T : set (real_line_metric R)) (V : set X) (ell : R) :
  (0<k)%N ->
  euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))!=0%R ->
  borel_set T -> borel_set V -> lebesgue_scalar_measure T=ell%:E ->
  @integral_geometric_measure R n k hkn 1 V< +oo ->
  is_measure_integral theta
    (partial_function_total (fun g=>projection_multiplicity_integral
      ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @`
        (T `*` (orthogonal_element_map (invO g) @` V))) F))
    ((inner_norm (@euclidean_inner_productP R (1+k))
      (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0)))*ell)%:E*
      ((@projection_beta R n k hkn 1)%:E*@integral_geometric_measure R n k hkn 1 V)).
Proof.
move=> hk haxis hT hV hell hfin.
pose ht := @orthogonal_probability_is_measure R n mulO theta htheta.
have [Q hQ] := @line_cylinder_projection_transverse_factor R n k F haxis.
pose Ap := orthogonal_projection_action (@euclidean_inner_productP R k)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO.
pose f g := projection_multiplicity_integral V (Ap g Q).
pose a := inner_norm (@euclidean_inner_productP R (1+k))
  (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))).
have hell0 : (0<=ell)%R.
  have hh := measure_nonnegative (@lebesgue_scalar_is_measure R) T.
  by rewrite hell lee_fin in hh.
have hcoef : 0<=(a*ell)%:E.
  rewrite lee_fin; exact: mulr_ge0 (inner_norm_nonnegative _ _) hell0.
have hi := @projection_orbit_multiplicity_integral R n k hkn mulO invO eO hO theta htheta V Q hk hV.
have hp g : 0<=f g := projection_multiplicity_integral_nonnegative (Ap g Q) hV.
have hs := @total_nonnegative_extended_scale_integral R O theta ht f _ (a*ell)%:E hp hi hcoef.
apply: (@measure_integral_almost_equal R O theta ht _ _ _ hs).
have hae := @finite_projection_orbit_almost_finite_integrals R n k hkn mulO invO eO hO
  theta htheta V Q hk hV hfin.
apply: (@measure_almost_everywhere_mono R O theta ht _ _ _ hae)=> g hgf.
have hnum : f g \is a fin_num by rewrite (ge0_fin_numE (hp g)).
have hrot : @borel_set X (orthogonal_element_map (invO g) @` V).
  exact (@orthogonal_source_image_borel R n mulO invO eO hO (invO g) V hV).
have hval : projection_multiplicity_integral (orthogonal_element_map (invO g) @` V) Q=(fine (f g))%:E.
  rewrite -(@projection_multiplicity_integral_orthogonal_action R n mulO invO eO hO k g Q V).
  exact: esym (fineK hnum).
have hc := hQ T (orthogonal_element_map (invO g) @` V) ell (fine (f g)) hT hrot hell hval.
exists ((a*ell)%:E*f g); split=> //.
change (projection_multiplicity_integral
  ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @`
    (T `*` (orthogonal_element_map (invO g) @` V))) F=(a*ell)%:E*f g).
by rewrite hc -(fineK hnum) -EFinM.
Qed.
End CylinderRotation.
