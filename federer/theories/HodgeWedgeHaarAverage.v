(** Federer (1969), 3.2.48, p. 286: the Haar
    average of the two complementary tangent words is
    beta_1(d,d-m)/beta_1(k,d-m). This supporting calculation
    applies the actual orthogonal-group integral of 2.7.16(6),
    p. 139, including empty complementary words. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates CoordinateProjection InnerProductUP InnerNorm InnerMetric
  InnerExteriorPositivity ExteriorGrading ExteriorMaps ExteriorNorm
  ExteriorHomogeneousProducts Bilinear LinearBasis AssociatedSubspace
  HodgeMaps HodgeUnitSimpleFactor ProductContraction ExteriorDiameterUP
  OrthogonalGroupTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures OrthogonalWedgeIntegrals TopologicalGroupUP
  HaarIntegralUP SummableRealFunctionUP CompactGroupHaarNormalisation IsotropyGroupTopology MeasureUP MeasureIntegralUP OrthogonalProjectionConstants
  ProjectionBeta GammaHalfSequences SphericalKinematicConstant RealPower RealPowerDivision RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hodge_wedge_haar_average]: supporting the exact
    isotropy average of 3.2.48, p. 286, after
    identifying the actual isotropy action with O(d).
    The result uses the actual normalized Haar measure and
    actual Hodge maps. Every zero degree and nontransverse
    pair is retained; both orientation signs have absolute
    value one and are removed only inside the norm. *)
Theorem hodge_wedge_haar_average (R:realType) (h2:(1+1:R)!=0) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (E:exterior_power (R_n R d) d)
    (x:exterior_power (R_n R d) k) (y:exterior_power (R_n R d) m)
    (mulS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (invS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (eS:euclidean_orthogonal_group R d)
    (theta:set (euclidean_orthogonal_group R d)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (euclidean_orthogonal_group R d) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  exterior_norm h2 (@euclidean_inner_productP R d) E= 1 ->
  simple x ->exterior_norm h2 (@euclidean_inner_productP R d) x= 1 ->
  simple y ->exterior_norm h2 (@euclidean_inner_productP R d) y= 1 ->
  is_measure_integral theta (real_total_integrand (fun g=>
    exterior_norm h2 (@euclidean_inner_productP R d)
      (exterior_product
        (exterior_power_map (hom_as_linear (orthogonal_element_map g)) (d-m)
          (hodge_vector h2 (@euclidean_inner_productP R d) E hm y))
        (hodge_vector h2 (@euclidean_inner_productP R d) E hk x))))
    ((gamma_half_sequence R k*gamma_half_sequence R m/
      (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)))%:E).
Proof.
move=>hS hTheta hE hsX hX hsY hY.
have [xi [a [hsXi [hXi [ha hStarY]]]]]:=@hodge_unit_simple_factor R h2
  (R_n R d) _ (@euclidean_inner_productP R d) d _ (@coordinate_basisP R d)
  E hE m hm y hsY hY.
have [eta [b [hsEta [hEta [hb hStarX]]]]]:=@hodge_unit_simple_factor R h2
  (R_n R d) _ (@euclidean_inner_productP R d) d _ (@coordinate_basisP R d)
  E hE k hk x hsX hX.
have hSwap:(d<=m+k)%N by rewrite addnC.
have hSum:((d-m)+(d-k)<=d)%N:=product_contraction_bound hm hk hSwap.
have hpk:(d-m<=k)%N by rewrite leq_subLR.
pose b1:=@projection_beta R d (d-m) (leq_subr m d) (1:R)%:E.
pose b2:=@projection_beta R k (d-m) hpk (1:R)%:E.
have hB1:=@projection_beta_specification R d (d-m) (leq_subr m d) (1:R)%:E (lexx _).
have hB2:=@projection_beta_specification R k (d-m) hpk (1:R)%:E (lexx _).
change (is_projection_constant (real_exterior_two_nonzero R) 1 d (d-m) b1) in hB1.
change (is_projection_constant (real_exterior_two_nonzero R) 1 k (d-m) b2) in hB2.
rewrite -(Prop_irrelevance h2 (real_exterior_two_nonzero R)) in hB1 hB2.
have hB2':is_projection_constant h2 1 (d-(d-k)) (d-m) b2.
  by rewrite subKn.
have hCore:=@orthogonal_wedge_integral R h2 d mulS invS eS hS
  (d-m)%N (d-k)%N 1 b1 b2 theta xi eta ltr01 hSum hB1 hB2' hTheta hsXi hsEta.
have hFunction:(fun g:euclidean_orthogonal_group R d=>
    exterior_norm h2 (@euclidean_inner_productP R d)
      (exterior_product
        (exterior_power_map (hom_as_linear (orthogonal_element_map g)) (d-m)
          (hodge_vector h2 (@euclidean_inner_productP R d) E hm y))
        (hodge_vector h2 (@euclidean_inner_productP R d) E hk x)))=
    (fun g=>real_power (exterior_norm h2 (@euclidean_inner_productP R d)
      (exterior_product (exterior_power_map (hom_as_linear (orthogonal_element_map g)) (d-m) xi) eta)) 1).
  apply:funext=>g; rewrite hStarX hStarY linearZ
    (bilZl (@exterior_product_bilinear R (R_n R d) (d-m) (d-k)))
    (bilZr (@exterior_product_bilinear R (R_n R d) (d-m) (d-k)))
    !exterior_norm_scale ha hb !mul1r real_power_one_exponent //.
  exact:exterior_norm_nonnegative.
rewrite -hFunction hXi hEta real_power_one_base !mulr1 in hCore.
rewrite (@real_power_negative_exponent R b2 1 hB2.1)
  (@real_power_one_exponent R b1 (ltW hB1.1))
  (@real_power_one_exponent R b2 (ltW hB2.1)) in hCore.
rewrite -(@spherical_kinematic_beta_ratio R d k m hm hpk).
exact hCore.
Qed.
