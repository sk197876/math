(** Federer (1969), 3.4.8(13), pp. 335–336:
    a positive original E_m reduction of an irreducible
    variety has m equal to its actual ideal depth.
    Apply the proved model (10), upper-null representative
    from (11), and positive measure of every nonempty
    m-dimensional analytic manifold germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  AnalyticGermRing CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder
  GermVanishingSealed IdealVarietyGermUP IdealVarietyGermSealed IdealVarietyGermExistence
  AnalyticReductionActual AnalyticReductionLociUP AnalyticReductionDepthUP AnalyticDepthSealed
  AnalyticRotatedGermIdeal AnalyticRotatedIdealDepth AnalyticRotatedIdealRecovery
  AnalyticPrimeLocalModelUP AnalyticPrimeLocalModelLaws Federer348PrimeReduction
  FunctionalAnalyticManifold AnalyticGermHigherDegreeNull SubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReductionDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_prime_positive_reduction_dimension]:
    the uniqueness of the possible positive E_m index
    in 3.4.8(13), pp. 335–336. The prime
    ideal is an actual vanishing ideal. No measure,
    model or dimension-comparison conclusion is assumed. *)
Theorem analytic_prime_positive_reduction_dimension (I:set G) (m:'I_n) (g:O):
  is_prime_commutative_ideal I ->(exists sigma:@set_germ_space E 0,I=ideal sigma) ->
  (0<m)%N ->
  @analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  depth I=(m:nat).
Proof.
move=>hPrime [sigma hVanishing] hPositive hEm.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hON:=@euclidean_coordinate_orthonormal_family R n.
have hTail:forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
  exact:((analytic_reduction_E_membership
    (@analytic_reduction_actual_laws R X B hB n e he omega I) m g).1 hEm).2.1.
have hDepthBound:(depth I<=m)%N.
  apply:(analytic_reduction_depth_minimal (@AnalyticDepth.laws R X B hB n e he omega I)).
  by exists g.
apply/eqP;rewrite eqn_leq hDepthBound /=.
case:(leqP m (depth I))=>// hSmall.
have hMN:(m<=n)%N:=ltnW (ltn_ord m).
have [k [first [U [d [b [f [Z [K [hI [hIg [hK [hModel hNonempty]]]]]]]]]]]]:=
  @federer_3_4_8_10 R n e he hON omega hDual I g m hMN hPrime hPositive hEm.
have hRecovered:=@given_vanishing_ideal_variety_recovery R X NX hNX 0 I hI sigma hVanishing.
have hZNonempty:=hNonempty hRecovered.
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
pose alpha:=@IdealVarietyGerm.value R X NX hNX 0 Ig hIg.
have hRotatedRecovery:=@analytic_rotated_ideal_variety_recovery R X B hB n e he
  I g hI hIg hRecovered.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have hRotatedDepth:=@analytic_rotated_ideal_depth R X B hB n e he omega mulO invO unitO hO I g.
have hAlphaDepth:(depth (ideal alpha)<m)%N.
  rewrite -hRotatedRecovery hRotatedDepth;exact:hSmall.
have hVariety:=@ideal_variety_germ_is_variety R X NX hNX 0 Ig alpha
  (@IdealVarietyGerm.laws R X NX hNX 0 Ig hIg).
have [S [hSGerm hNull]]:=@analytic_germ_higher_degree_null_representative R n alpha m hVariety hAlphaDepth.
have hFields:=hModel.
do 15 (case:hFields=>_ hFields).
have hManifold:=functional_analytic_submanifold_analytic hFields.1.
have hJoin:=analytic_prime_local_model_variety hModel.
have hSub:set_germ_subset (@set_germ E 0 Z) (@set_germ E 0 S).
  rewrite hSGerm /alpha hJoin;exact:set_germ_subset_join_right.
exfalso;exact:(analytic_submanifold_germ_nonnull hManifold hZNonempty hSub hNull).
Qed.
End ReductionDimension.
