(** Federer (1969), 3.4.8(10), pp. 332–333:
    the actual local model has nonempty
    remainder germ under the original
    vanishing-ideal hypothesis. Transfer that hypothesis
    through the actual orthogonal map and
    apply the original contradiction argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness OrthogonalGroupTopology AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  CommutativeIdealUP SetGermUP GermVanishingSealed IdealVarietyGermSealed AnalyticRotatedGermIdeal
  AnalyticPrefixGermMap AnalyticPrimeLocalModelUP AnalyticPrimeLocalModelLaws AnalyticRotatedIdealRecovery
  AnalyticPrimeVarietyNonempty.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nonempty.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable P:Hom X Y.
Variable I:set G.
Variable g:@orthogonal_group R X B hB n e he.
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Variable hI:is_finitely_generated_commutative_ideal I.
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m).
Variable U:set Y.
Variable d:@analytic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m)->'I_k->@analytic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m)->@analytic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set G.
Variable hK:is_finitely_generated_commutative_ideal K.

(** Source for [analytic_prime_local_model_nonempty_original]:
    gamma_0(Z) differs from the empty
    germ when I=ideal(var I),
    3.4.8(10), pp. 332–333.
    The hypothesis concerns the original I;
    its transfer to I_g is proved. *)
Theorem analytic_prime_local_model_nonempty_original:
  @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  I = @AnalyticSetIdeal.value R X NX hNX 0 (@IdealVarietyGerm.value R X NX hNX 0 I hI) ->
  @set_germ Top 0 Z<>@set_germ Top 0 set0.
Proof.
move=>hModel hRecovered.
have hRotated:=@analytic_rotated_ideal_variety_recovery R X B hB n e he I g hI hIg hRecovered.
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega m hMN.
have hOutside:=@analytic_prime_local_model_delta_outside R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hEnlarged:=@analytic_prime_local_model_enlarged_ideal R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hVariety:=@analytic_prime_local_model_variety R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hContains:K (E (analytic_germ d)).
  apply:(generated_commutative_ideal_contains hEnlarged);right;by [].
exact:(@analytic_variety_remainder_nonempty R X NX hNX 0 Ig K hIg hK
  (E (analytic_germ d)) (@set_germ Top 0 Z) hRotated hOutside hContains hVariety).
Qed.
End Nonempty.
