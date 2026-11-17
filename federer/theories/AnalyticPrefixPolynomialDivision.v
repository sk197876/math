(** Federer (1969), 3.4.8(10), p. 331:
    division inside an original coordinate
    prefix retains its quotient and bounded
    polynomial remainder in that prefix.
    Apply the existing exact prefix diagrams
    and original-centre analytic division. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanScalarCoordinateMaps
  EuclideanStiefelInnerSplitting OrthonormalFamilies OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermValueSealed AnalyticCoordinateGermsSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixGermInjective
  AnalyticPrefixNestedComposition AnalyticPrefixCoordinateGerm AnalyticPrefixWeierstrassSplit
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionCoordinateRegularWitness
  AnalyticOriginalPreparedPolynomial WeierstrassRegularUP WeierstrassFunctionalPower
  CommutativeIdealUP NoetherianRingSurjection CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed CommutativePolynomialEvaluationLaws PolynomialScalarComposition
  DistinguishedPolynomialUP AnalyticPrefixGermSubring AnalyticOriginalPolynomialDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixDivision.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable m:'I_n.
Local Notation Y:=(R_n R (m:nat).+1).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (m:nat).+1)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (m:nat).+1)).
Local Notation Z:=(R_n R (m:nat)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (m:nat))).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (m:nat))).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R Z NZ hNZ 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation hMN:=(leq_trans (leqnSn (m:nat)) (ltn_ord m)).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation Gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega m).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.


(** Source for [analytic_prefix_distinguished_division]:
    the original analytic division used in
    the induction over Q_j, 3.4.8(10),
    p. 331. Both quotient and remainder
    retain the original next prefix, and
    the coefficient germs remain at zero.
    No division or coefficient-independence proof is repeated. *)
Theorem analytic_prefix_distinguished_division (H:P) k:
  is_distinguished_polynomial coefficient (@AnalyticGermValue.map R Z NZ hNZ 0) H k ->
  (0<k)%N ->forall alpha:G,
    @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) alpha ->
  exists a:G,exists r:P,
    (forall i,(k<=i)%N ->coefficient r i = 0) /\
    alpha = a*J H+J r /\
    @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) a.
Proof.
move=>hDistinguished hK alpha hPrefix.
have [beta hBeta]:=(@analytic_prefix_germ_subring_membership R X NX hNX n e he omega
  (m:nat).+1 (ltn_ord m) alpha).1 hPrefix.
pose omegaY:=fun i:'I_(m:nat).+1=>@euclidean_scalar_coordinate_map R (m:nat).+1 i.
pose projection:=@AnalyticPrefixCoordinates.projection R Y (m:nat).+1 omegaY (m:nat) (leqnSn (m:nat)).
pose section:=@AnalyticPrefixCoordinates.inclusion R Y (m:nat).+1 (@coordinate_basis R (m:nat).+1)
  (m:nat) (leqnSn (m:nat)).
have hProjection:=@AnalyticPrefixCoordinates.projection_laws R Y (m:nat).+1 omegaY (m:nat) (leqnSn (m:nat)).
have hSection:=@AnalyticPrefixCoordinates.inclusion_laws R Y (m:nat).+1 (@coordinate_basis R (m:nat).+1)
  (m:nat) (leqnSn (m:nat)).
have hDualY i l:omegaY i (@coordinate_basis R (m:nat).+1 l) = if i==l then 1 else 0.
  by rewrite /omegaY /euclidean_scalar_coordinate_map /= /coordinate_basis ffunE eq_sym.
have hSplit:=@analytic_last_coordinate_prefix_split R Y (@euclidean_inner_product R (m:nat).+1)
  (@euclidean_inner_productP R (m:nat).+1) (m:nat) (@coordinate_basis R (m:nat).+1)
  (@coordinate_basisP R (m:nat).+1) (@euclidean_coordinate_orthonormal_family R (m:nat).+1)
  omegaY hDualY projection section hProjection hSection.
pose xi:=omegaY ord_max.
have hXi:=@euclidean_scalar_coordinate_bounded R (m:nat).+1 ord_max.
have [fXi [hXiValues _]]:=@weierstrass_functional_power_representative R Y NY hNY xi 1 hXi.
have hValues y:analytic_representative_value fXi y = xi y by rewrite hXiValues expr1.
pose EB:=@analytic_prefix_germ_map R Y NY hNY (m:nat).+1 (@coordinate_basis R (m:nat).+1)
  (@coordinate_basisP R (m:nat).+1) omegaY (m:nat) (leqnSn (m:nat)).
have hEB:=@analytic_prefix_germ_map_specification R Y NY hNY (m:nat).+1 (@coordinate_basis R (m:nat).+1)
  (@coordinate_basisP R (m:nat).+1) omegaY (m:nat) (leqnSn (m:nat)).
have hComposition a:E a = E1 (EB a).
  exact:(@analytic_adjacent_prefix_germ_composition R X NX hNX n omega (m:nat) hMN (ltn_ord m)
    (@AnalyticPrefixCoordinates.projection R X n omega (m:nat) hMN)
    (@AnalyticPrefixCoordinates.projection R X n omega (m:nat).+1 (ltn_ord m)) projection E E1 EB
    (@AnalyticPrefixCoordinates.projection_laws R X n omega (m:nat) hMN)
    (@AnalyticPrefixCoordinates.projection_laws R X n omega (m:nat).+1 (ltn_ord m)) hProjection
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (m:nat) hMN)
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (m:nat).+1 (ltn_ord m)) hEB a).
have hCoordinate:E1 (analytic_germ fXi) = Gamma.
  apply:(@analytic_prefix_last_coordinate_germ R X NX hNX n e he omega m fXi)=>y.
  exact:hValues y.
pose JY:=@CommutativePolynomialEvaluation.map A P A1 embed variable coefficient hP EB (analytic_germ fXi).
have hJY:=@CommutativePolynomialEvaluation.laws A P A1 embed variable coefficient hP EB (analytic_germ fXi).
pose composite:{rmorphism P->G}:=GRing.RMorphism.clone P G (E1 \o JY) _.
have hComposite:=@polynomial_evaluation_after_ring_map A P A1 G embed variable EB (analytic_germ fXi) JY E1 hJY.
have hCompositeOriginal:is_commutative_polynomial_evaluation embed variable E Gamma composite.
  apply:(polynomial_evaluation_change_parameters hComposite).
  - move=>a;exact:esym (hComposition a).
  - exact:hCoordinate.
have hJEquation T:J T = E1 (JY T).
  exact:(@polynomial_evaluation_unique A P G embed variable coefficient hP E Gamma J composite hJ hCompositeOriginal T).

have [a [r [hSupport hDivision]]]:=@analytic_original_distinguished_division R Y Z NY NZ hNY hNZ
  (@coordinate_basis R (m:nat).+1 ord_max) xi section projection hSplit fXi hXi hValues EB hEB
  P embed variable coefficient hP JY hJY H k hDistinguished hK beta.
exists (E1 a),r;split;first exact:hSupport.
split.
- by rewrite -hBeta hDivision rmorphD rmorphM -!hJEquation.
- apply/analytic_prefix_germ_subring_membership;by exists a.
Qed.
End PrefixDivision.
