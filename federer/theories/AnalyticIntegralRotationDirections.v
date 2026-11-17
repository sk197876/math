(** Federer (1969), 3.4.8(8), p. 330:
    original integral relations give every
    required positive directional witness after
    an original Q_m rotation. Keep the
    original coefficient ring and use actual
    monic line representatives and Taylor coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies NormFiniteLinearBound GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives PointedFunctionalGermExistence
  AnalyticCoordinateGermsSealed AnalyticPrefixCoordinatesSealed AnalyticPrefixBasisValues
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixGermSubring AnalyticPrefixGermSubringLaws
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixPolynomialSubring AnalyticPrefixSubringMonotonicity
  AnalyticOrthogonalPullback AnalyticRotatedGermIdeal AnalyticRotatedCompositionInverse AnalyticFixedPrefixPullback
  AnalyticReductionActual AnalyticReductionLociUP AnalyticMonicLineJet AnalyticMonicPrefixRepresentative
  CommutativeQuotientUP CommutativeSubringUP CommutativeSubringLaws IntegralRingElementUP OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IntegralDirections.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Variable g:O.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Hypothesis hIntegral:forall c:C,is_integral_ring_element scalar c.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega).
Local Notation H:=(@analytic_suffix_rotation_group R X B hB n e he m).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_integral_suffix_rotation_B]: the
    original integral quotient supplies B_j
    after an original Q_m rotation,
    3.4.8(8), p. 330. In fact this
    deduction holds for every original suffix
    rotation. Monicity gives a nonzero
    highest directional coefficient without requiring
    lower coefficients to vanish at zero. *)
Theorem analytic_integral_suffix_rotation_B (q:H) (j:'I_n):
  (m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j (mulO g (set_val q)).
Proof.
move=>hMJ.
pose pullback:=@analytic_orthogonal_germ_map R X B hB n e he (invO (set_val q)).
have hInverseQ:H (invO (set_val q)).
  rewrite -(subgroup_restriction_inv hH q);exact:set_valP (invH q).
have hFixed:=@analytic_fixed_prefix_germ R X B hB n e he hON omega hDual m
  (invO (set_val q)) hInverseQ hMN.
pose c:=pi (pullback (gamma j)).
have [k [beta [hK hRelation]]]:=hIntegral c.
pose Phi:G:=(gamma j)^+k-\sum_(i<k) E (beta i)*(gamma j)^+(i:nat).
have hIdeal:@analytic_rotated_germ_ideal R X B hB n e he I (mulO g (set_val q)) Phi.
  apply:(@analytic_rotated_composition_inverse R X B hB n e he mulO invO unitO hO I g (set_val q) Phi).2.
  apply:(commutative_quotient_kernel hPi _).1.
  change (pi (pullback Phi) = 0).
  rewrite /Phi !rmorphB !rmorph_sum !rmorphXn.
  under eq_bigr do rewrite !rmorphM !rmorphXn hFixed.
  change (c^+k-\sum_(i<k) scalar (beta i)*c^+(i:nat) = 0).
  by rewrite hRelation subrr.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
have hRing:is_commutative_subring (Q (j:nat).+1).
  rewrite (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)).
  exact:(@analytic_prefix_germ_subring_laws R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)).
have hGamma:Q (j:nat).+1 (gamma j).
  rewrite (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)).
  exact:(@analytic_next_prefix_coordinate_member R X NX hNX n e he omega j).
have hCoefficients a:Q (j:nat).+1 (E a).
  apply:(@analytic_coordinate_prefix_subring_monotone R X NX hNX n e he omega m (j:nat).+1
    (leq_trans hMJ (leqnSn (j:nat))) (ltn_ord j)).
  rewrite (analytic_coordinate_subring_family_member hQLaws hMN).
  apply/analytic_prefix_germ_subring_membership;by exists a.
have hPowers i:Q (j:nat).+1 ((gamma j)^+i):=@commutative_subring_power G _ hRing (gamma j) i hGamma.
have hSum:Q (j:nat).+1 (\sum_(i<k) E (beta i)*(gamma j)^+(i:nat)).
  apply:(commutative_subring_finite_sum hRing)=>i _ _.
  exact:(@commutative_subring_multiply G _ hRing _ _ (hCoefficients (beta i)) (hPowers i)).
have hMember:Q (j:nat).+1 Phi.
  exact:(@commutative_subring_add G _ hRing _ _ (hPowers k)
    (@commutative_subring_opp G _ hRing _ hSum)).
pose P:=@AnalyticPrefixCoordinates.projection R X n omega m hMN.
have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega m hMN.
have hPZero:=@analytic_prefix_basis_outside R X n e omega m hMN P hP hDual j hMJ.
have hE:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega m hMN.
have hBound:=@norm_finite_linear_bounded R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) n e he (omega j).
have [fXi hF]:=@pointed_functional_representative_exists R X NX hNX 0 (omega j) hBound.
have hValues x:analytic_representative_value fXi x = omega j x by rewrite hF subr0.
have hGerm:=@AnalyticCoordinateGerms.laws R X NX hNX n e he omega j fXi hValues.
have hXiOne:omega j (e j) = 1 by rewrite hDual eqxx.
have [f [a [hRep hLine]]]:=@analytic_monic_prefix_line_representative R X (R_n R m) NX
  (inner_norm (@euclidean_inner_productP R m)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R m)) P E (omega j) fXi k beta (e j)
  hE hValues hPZero hXiOne.
rewrite hGerm in hRep.
have hJet:=@analytic_monic_line_nonzero_directional_jet R X NX hNX f k (e j) a hK hLine.
rewrite hRep in hJet.
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
apply:(analytic_reduction_B_membership hLoci j (mulO g (set_val q))).2.
by exists Phi.
Qed.
End IntegralDirections.
