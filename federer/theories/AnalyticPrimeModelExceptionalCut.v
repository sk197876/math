(** Federer (1969), 3.4.8(11), p. 334:
    connect the original prime model of (10) to
    its actual exceptional cut and regular difference.
    The original beta supplies the strict enlarged
    vanishing ideal. All prefix representatives and
    generated exceptional ideals are chosen in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis OrthonormalFamilies GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRing AnalyticGermRingLaws CommutativeIdealUP
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermCutDifference SetGermRegularCut
  GermVanishingSealed GermVanishingIdeal GermVanishingMonotonicity AnalyticVarietyGermUP
  AnalyticVarietyGermBooleanClosure AnalyticProperSubgermIdeal IdealVarietyGermUP IdealVarietyGermSealed
  IdealVarietyGermOrder IdealVarietyAdjoinEquation AnalyticZeroGermSealed AnalyticRotatedGermIdeal
  AnalyticRotatedIdealPrime AnalyticReductionActual AnalyticDepthSealed AnalyticPrimeLocalModelUP
  AnalyticPrimeLocalModelLaws AnalyticPrimePrefixExceptionalCut AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExceptionalModel.
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
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Variable hON:orthonormal_family B e.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
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

Local Notation C:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation alpha:=(@IdealVarietyGerm.value R X NX hNX 0 Ig hIg).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation germ:=(@set_germ Top 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_prime_model_exceptional_cut]:
    the original enlarged K, strict dimension drop,
    and exact regular D germ in 3.4.8(11),
    p. 334. The preceding model's larger-ideal
    conclusion supplies chi. No exceptional cut,
    variety split or dimension conclusion is assumed. *)
Theorem analytic_prime_model_exceptional_cut (beta:@set_germ_space Top 0):
  is_prime_commutative_ideal I ->(0<m)%N ->
  @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  Ig = ideal alpha ->
  @is_analytic_variety_germ R X NX hNX 0 beta ->~set_germ_subset alpha beta ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  exists chi:PY,exists L:set G,exists hL:is_finitely_generated_commutative_ideal L,
    is_generated_commutative_ideal
      (Ig `|` [set phi:G|phi = E ((analytic_germ chi:C)*analytic_germ d)]) L /\
    Ig `<=` L /\L `<=` ideal (@SetGerms.meet Top 0 alpha beta) /\
    (let gamma:=@IdealVarietyGerm.value R X NX hNX 0 L hL in
      set_germ_subset gamma alpha /\
      set_germ_subset (@SetGerms.meet Top 0 alpha beta) gamma /\
      gamma = @SetGerms.meet Top 0 alpha
        (germ [set x|vy chi (P x)*vy d (P x)=0]) /\
      (gamma = germ set0 \/(depth (ideal gamma)<m)%N) /\
      @SetGerms.meet Top 0 alpha (@SetGerms.neg Top 0 gamma) =
        germ [set x|Z x /\vy chi (P x)<>0] /\
      @SetGerms.meet Top 0 alpha (@SetGerms.neg Top 0 beta) =
        @SetGerms.join Top 0 (@SetGerms.meet Top 0 gamma (@SetGerms.neg Top 0 beta))
          (germ [set x|Z x /\vy chi (P x)<>0])).
Proof.
move=>hPrime hPositive hModel hRecovered hBeta hNotContained hTail.
pose sigma:=@SetGerms.meet Top 0 alpha beta.
pose J:=ideal sigma.
have hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 Ig alpha
    (@IdealVarietyGerm.laws R X NX hNX 0 Ig hIg)).
have hSigma:@is_analytic_variety_germ R X NX hNX 0 sigma.
  exact:analytic_variety_germ_intersection hAlpha hBeta.
have hDifferent:alpha<>sigma by move=>h;apply:hNotContained;exact:esym h.
have [eta [hJEta hNotEta]]:=analytic_proper_subgerm_ideal_witness hSigma
  (set_germ_meet_subset_left alpha beta) hDifferent.
have hIJ:Ig `<=` J.
  rewrite hRecovered;exact:analytic_set_ideal_antitone (set_germ_meet_subset_left alpha beta).
have hLarger:=hModel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.
have hStrict:exists eta:G,J eta /\~Ig eta.
  exists eta;split;first exact:hJEta.
  by rewrite hRecovered.
have [theta [hTheta [hQ [hOutside hNonzero]]]]:=hLarger J
  (analytic_set_ideal_ring_laws sigma) hIJ hStrict.
have hDelta:=@analytic_prime_local_model_delta_outside R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hPrimeRotated:=@analytic_rotated_germ_ideal_prime R X B hB n e he I g hPrime.
have hTailPositive:(0<n-m)%N:=leq_ltn_trans (leq0n (first:nat)) (ltn_ord first).
have hMNStrict:(m<n)%N by move:hTailPositive;rewrite subn_gt0.
pose mIndex:'I_n:=Ordinal hMNStrict.
have [chi [L [hL [hChi [hChiOutside [hGenerated [hIL [hLJ [hPhi [hPhiOutside hDimension]]]]]]]]]]:=
  @analytic_prime_prefix_exceptional_cut R X B hB n e he hON omega hDual I g mIndex hMN J d
    hPositive hPrimeRotated (analytic_set_ideal_ring_laws sigma) hIJ hDelta
    (ex_intro _ theta (conj hTheta (conj hQ hOutside))) hTail.
pose gamma:=@IdealVarietyGerm.value R X NX hNX 0 L hL.
have hGammaAlpha:set_germ_subset gamma alpha:=ideal_variety_germ_antitone hIg hL hIL.
have hSigmaGamma:set_germ_subset sigma gamma:=ideal_variety_germ_contains_vanishing_set hL hLJ.
have hAdjoin:=@ideal_variety_adjoin_equation R X NX hNX 0 Ig L hIg hL
  (E ((analytic_germ chi:C)*analytic_germ d)) hGenerated.
pose phi:=@analytic_multiply_representatives R Y NY hNY 0 chi d.
have hPhiGerm:analytic_germ phi = (analytic_germ chi:C)*analytic_germ d.
  by rewrite /phi -(@analytic_germ_multiply_equation R Y NY hNY 0 _ _ _ (@AnalyticGerms.laws R Y NY hNY 0)).
have [p [hP hValue]]:=(@analytic_prefix_germ_map_specification R X NX hNX n e he omega m hMN) phi.
have hPOriginal:analytic_germ p = E ((analytic_germ chi:C)*analytic_germ d).
  by rewrite -hP hPhiGerm.
have hZero:@AnalyticZeroGerm.value R X NX hNX 0 (E ((analytic_germ chi:C)*analytic_germ d)) =
    germ [set x|vy chi (P x)*vy d (P x)=0].
  rewrite -(@AnalyticZeroGerm.laws R X NX hNX 0 _ p hPOriginal).
  congr (germ _);apply:funext=>x.
  change ((analytic_representative_value p x=0) = (vy chi (P x)*vy d (P x)=0)).
  by rewrite hValue.
have hCut:gamma = @SetGerms.meet Top 0 alpha (germ [set x|vy chi (P x)*vy d (P x)=0]).
  by rewrite /gamma hAdjoin hZero.
have hKGenerated:=@analytic_prime_local_model_enlarged_ideal R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hKL:L `<=` K.
  apply:(generated_commutative_ideal_minimal hGenerated (generated_commutative_ideal_laws hKGenerated)).
  move=>phi0 [hIgPhi|->].
  - apply:(generated_commutative_ideal_contains hKGenerated);by left.
  - rewrite rmorphM.
    have hDeltaK:K (E (analytic_germ d)).
      apply:(generated_commutative_ideal_contains hKGenerated);by right.
    exact:(@commutative_ideal_mul G K (generated_commutative_ideal_laws hKGenerated)
      (E (analytic_germ chi)) (E (analytic_germ d)) hDeltaK).
have hOldExceptional:set_germ_subset (@IdealVarietyGerm.value R X NX hNX 0 K hK) gamma.
  exact:ideal_variety_germ_antitone hL hK hKL.
have hVariety:=@analytic_prime_local_model_variety R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hZEquation:=hModel.2.2.2.2.2.2.2.2.2.1.
have hNonzeroDelta x (hx:Z x):vy d (P x)<>0.
  apply/eqP;exact:((hZEquation x).1 hx).2.2.
have hRegular:=@set_germ_regular_product_cut Top R 0 alpha
  (@IdealVarietyGerm.value R X NX hNX 0 K hK) gamma Z
  (fun x=>vy chi (P x)) (fun x=>vy d (P x)) hVariety hOldExceptional hCut hNonzeroDelta.
exists chi,L,hL;split;first exact:hGenerated.
split;first exact:hIL.
split;first exact:hLJ.
split;first exact:hGammaAlpha.
split;first exact:hSigmaGamma.
split;first exact:hCut.
split;first exact:hDimension.
split;first exact:hRegular.
rewrite -hRegular;exact:set_germ_cut_difference_split hGammaAlpha hSigmaGamma.
Qed.
End ExceptionalModel.
