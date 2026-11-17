(** Federer (1969), 3.4.8(8), p. 330:
    primitive generation supplies the original
    C_m denominators and relations after the
    original rotation. Reuse original denominator
    representatives, fixed coefficient germs, polynomial
    prefix membership and inverse ideal transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  AnalyticGermRing AnalyticCoordinateGermsSealed AnalyticPrefixGermMap AnalyticPrefixGermSubring
  AnalyticCoordinateSubringFamilySealed AnalyticCoordinateSubringFamilyUP
  AnalyticOrthogonalPullback AnalyticRotatedGermIdeal AnalyticRotatedCompositionInverse
  AnalyticReductionActual AnalyticReductionLociUP AnalyticFixedPrefixPullback AnalyticPrefixPolynomialSubring
  CommutativeQuotientUP CommutativeSubringUP FractionFieldUP CoefficientFractionFieldUP CoefficientFractionFieldLaws
  CommutativePolynomialSealed CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialScalarComposition PrimitiveFieldOriginalRepresentative OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Relations.
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
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Hypothesis hFraction:is_commutative_fraction_field inclusion.
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Hypothesis hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation H:=(@analytic_suffix_rotation_group R X B hB n e he m).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_reduction_primitive_rotation_C]:
    every original primitive rotation gives
    the original C_m relations, 3.4.8(8),
    p. 330. Each denominator lies in
    the original Q_m outside I_(gq), and
    each numerator lies in the original
    Q_(m+1). No such relation is assumed. *)
Theorem analytic_reduction_primitive_rotation_C (q:H):
  is_generated_commutative_subring
    (fun y:L=>y = inclusion (pi (@analytic_orthogonal_germ_map R X B hB n e he
      (invO (set_val q)) (gamma m))) \/exists a:M,y = phi a) setT ->
  @analytic_reduction_actual_C R X B hB n e he omega I m (mulO g (set_val q)).
Proof.
move=>hGenerated.
pose pullback:=@analytic_orthogonal_germ_map R X B hB n e he (invO (set_val q)).
have hInverseQ:H (invO (set_val q)).
  rewrite -(subgroup_restriction_inv hH q);exact:set_valP (invH q).
have hFixed:=@analytic_fixed_prefix_germ R X B hB n e he hON omega hDual m
  (invO (set_val q)) hInverseQ hMN.
pose P:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A P G embed variable coefficient hP E (gamma m).
have hJ:=@CommutativePolynomialEvaluation.laws A P G embed variable coefficient hP E (gamma m).
pose composite:{rmorphism G->C}:=GRing.RMorphism.clone G C (pi \o pullback) _.
pose EC:{rmorphism P->C}:=GRing.RMorphism.clone P C (composite \o J) _.
have hBase:=@polynomial_evaluation_after_ring_map A P G C embed variable E (gamma m) J composite hJ.
have hEC:is_commutative_polynomial_evaluation embed variable scalar (pi (pullback (gamma m))) EC.
  apply:(polynomial_evaluation_change_parameters hBase).
  - move=>a;change (pi (pullback (E a)) = pi (E a));by rewrite hFixed.
  - by [].
pose hJN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
have hJBound:is_commutative_polynomial_evaluation embed variable
    (@analytic_prefix_germ_map R X NX hNX n e he omega m hJN) (gamma m) J.
  apply:(polynomial_evaluation_change_parameters hJ).
  - move=>a;by rewrite (bool_irrelevance hMN hJN).
  - by [].
have hNumerator H0:@analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) (J H0).
  exact:(@analytic_prefix_polynomial_member R X NX hNX n e he omega m P embed variable coefficient hP J hJBound H0).
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hQ:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
apply:(analytic_reduction_C_membership hLoci m (mulO g (set_val q))).2.
move=>j hMJ.
pose c:=pi (pullback (gamma j)).
have [delta [H0 [hDelta hRelation]]]:=@primitive_field_original_coefficient_representative
  A P C L M embed variable coefficient hP scalar inclusion eta phi (pi (pullback (gamma m))) EC
  hFraction hCoefficient hEC hGenerated c.
exists (E delta),(J H0);split.
- rewrite (analytic_coordinate_subring_family_member hQ hMN).
  apply/analytic_prefix_germ_subring_membership;by exists delta.
- split.
  + move=>hIn.
    have hOriginal:=(@analytic_rotated_composition_inverse R X B hB n e he mulO invO unitO hO
      I g (set_val q) (E delta)).1 hIn.
    have hZero:pi (pullback (E delta)) = 0:=(commutative_quotient_kernel hPi _).2 hOriginal.
    rewrite hFixed in hZero.
    apply:hDelta;apply:(@coefficient_fraction_scalar_kernel A L M
      (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi hCoefficient delta).2.
    change (inclusion (pi (E delta)) = 0);by rewrite hZero rmorph0.
  + split.
    * rewrite (analytic_coordinate_subring_family_member hQ (ltn_ord m));exact:hNumerator.
    * apply:(@analytic_rotated_composition_inverse R X B hB n e he mulO invO unitO hO
        I g (set_val q) (E delta*gamma j-J H0)).2.
      apply:(commutative_quotient_kernel hPi _).1.
      change (pi (pullback (E delta*gamma j-J H0)) = 0).
      rewrite !rmorphB !rmorphM hFixed.
      change (scalar delta*c-EC H0 = 0);by rewrite hRelation subrr.
Qed.
End Relations.
