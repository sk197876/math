(** Federer (1969), 4.1.5, p. 349:
    necessity of the original finite-gauge criterion.
    On the compact support of f in K(U)+,
    its uniform norm bounds every admissible test.
    The original compact dual-norm integral then
    bounds all S(phi) by the ordinary integral
    comparison of Chapter 2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP ContinuousDualUP WeakEvaluationTopologyUP
  FunctionLatticeUP CompactSupportFunctionUP UniformFunctionNormUP UniformFunctionNorm
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic
  RealSubsetIntegralGraph VectorDaniellPairingMeasurability DistributionIntegralFieldUP
  DistributionIntegrationRepresentationUP DistributionVariationUP DistributionVariationBoundedExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_representation_finite_gauge]:
    the condition is necessary for an arbitrary original
    Radon representation with locally integrable dual
    norm, Federer 4.1.5, p. 349. The density
    need not be normalized or bounded. *)
Theorem distribution_representation_finite_gauge (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o)
    (rho:set X->\bar R) (xi:X->D):
  is_distribution_integration_representation hD hO value S rho xi ->
  forall f:X->R,positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    exists b:R,is_distribution_variation_value NY value S f b%:E.
Proof.
move=>hRepresentation f hf.
have hm:=distribution_representation_measure hRepresentation.
pose K:=@real_function_support R X f.
pose B:=@compact_support_uniform_norm R X f.
have hBSpec:=@compact_support_uniform_norm_specification R X f hf.1.
have hB:0<=B:=uniform_function_norm_nonnegative hBSpec.
have hFBound:forall x,f x<=B.
  move=>x; exact:le_trans (ler_norm _) (uniform_function_norm_bound hBSpec x).
have[c hLocal]:=@distribution_representation_compact_norm R X Y NY hNY D ed DN hD O hO
  E value S rho xi hRepresentation K hf.1.2.
pose G:=fun x:X=>if pselect (K x) then DN (xi x) else 0.
have hGOn:forall x,K x ->G x=DN (xi x).
  by move=>x hx; rewrite /G; case:pselect.
have hGOff:forall x,~K x ->G x=0.
  by move=>x hx; rewrite /G; case:pselect.
have hGIntegral:=(@real_subset_integral_total R X rho K (fun x=>DN (xi x)) G c%:E
  hGOn hGOff).1 hLocal.
have hScaled:=@real_total_integral_scale R X rho hm G c B hGIntegral.
apply:(@distribution_variation_bounded_value_exists R X Y NY hNY E value S f (B*c) hf.2)=>phi hPhi.
have hOriginal:=distribution_representation_action hRepresentation phi.
have hPointwise:forall x,`|ed (xi x) (value phi x)|<=B*G x.
  move=>x; case:(pselect (K x))=>hx.
  - rewrite (hGOn x hx).
    have hNorm:=continuous_dual_norm_laws hD (xi x).
    have hEval:=real_functional_norm_bound hNorm (value phi x).
    have hPhiB:=le_trans (hPhi x) (hFBound x).
    have hBound:=ler_wpM2l (real_functional_norm_nonnegative hNorm) hPhiB.
    rewrite mulrC; exact:le_trans hEval hBound.
  - have hFZero:f x=0:=@real_function_zero_off_support R X f x hx.
    have hNormZero:NY (value phi x)=0.
      apply/eqP; rewrite eq_le (real_seminorm_nonnegative hNY.1 _) andbT.
      by rewrite -hFZero; exact:hPhi x.
    rewrite (hNY.2 _ hNormZero) linear0 normr0 (hGOff x hx) mulr0.
    exact:lexx.
have[a [hA hAbs]]:=@real_total_dominated_integral R X rho hm
  (fun x=>ed (xi x) (value phi x)) (fun x=>B*G x) (B*c) hOriginal.1 hScaled hPointwise.
have hEq:a=S phi.
  have h:=measure_integral_unique hA hOriginal; by injection h.
rewrite hEq in hAbs.
exact:le_trans (ler_norm _) hAbs.
Qed.
