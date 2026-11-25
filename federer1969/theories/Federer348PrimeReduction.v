(** Federer (1969), 3.4.8(10), pp. 327, 330–333:
    the complete original prime-ideal local
    reduction theorem, including its nonempty-germ
    conclusion under I=ideal(var I).
    All objects remain local witnesses to
    the independently specified model laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis OrthonormalFamilies GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology NormDifferentialUP NormFiniteLinearBound
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticCoordinateGermsSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionOriginalEquations
  SetGermUP SetGermSealed AnalyticZeroGermSealed IdealVarietyGermSealed
  CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PointedFunctionalGermExistence OriginalPolynomialCylinderWitnesses OrdinalCoordinateTail
  AnalyticPrimeLocalModelUP AnalyticPrimeLocalModelAssembly AnalyticReductionPrimeModelExistence
  AnalyticGermNoetherian GermVanishingSealed AnalyticPrimeLocalModelNonempty.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalPrimeModel.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable I:set G.
Variable g:@orthogonal_group R X B hB n e he.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation Y:=(R_n R m).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation PX:=(@analytic_representative_type R X NX hNX 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation vx:=(@analytic_representative_value R X NX hNX 0).
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).

(** Source for [federer_3_4_8_10]:
    the original positive-dimensional prime reduction,
    3.4.8(10), pp. 327, 330–333.
    Retain the original E_m membership,
    all defining equations and coefficient values,
    variety decomposition, nonvanishing derivative,
    functional submanifold, component homeomorphisms,
    larger-ideal assertion and nonempty-germ conclusion. *)
Theorem federer_3_4_8_10:
  is_prime_commutative_ideal I ->(0<m)%N ->
  @analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  exists k (first:'I_(n-m)) (U:set Y) (d:PY) (b:'I_(n-m)->'I_k->PY)
    (f:'I_(n-m)->PX) (Z:set X) (K:set G),
    exists (hI:is_finitely_generated_commutative_ideal I)
      (hIg:is_finitely_generated_commutative_ideal Ig) (hK:is_finitely_generated_commutative_ideal K),
      @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK /\
      (I = @AnalyticSetIdeal.value R X NX hNX 0 (@IdealVarietyGerm.value R X NX hNX 0 I hI) ->
        @set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 Z <>
        @set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 set0).
Proof.
move=>hPrime hPositive hEm.
have [k [first [U [d [b [f [Z [K data]]]]]]]]:=
  @analytic_reduction_prime_local_model_exists R n e he hON omega hDual I g m hMN hPrime hPositive hEm.
have [hIg [hK hModel]]:=data.
have hI:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he I hPrime.1.
exists k,first,U,d,b,f,Z,K,hI,hIg,hK;split;first exact:hModel.
move=>hRecovered.
exact:(@analytic_prime_local_model_nonempty_original R n m hMN e he omega P I g hI hIg
  k first U d b f Z K hK hModel hRecovered).
Qed.
End OriginalPrimeModel.
