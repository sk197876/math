(** Federer (1969), 3.4.8(11), p. 333:
    at every centre a of the compact
    ball, the critical variety has smaller dimension
    if Psi is not locally constant there.
    Translate the actual equations and differential;
    apply the original zero-centred depth theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies NormDifferentialUP NormDifferentialLocal NormClassOneNormalization
  SetGermUP FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed
  AnalyticSourceTranslation AnalyticCriticalGermDimensionDrop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_critical_centre_depth_drop]:
    the smaller critical-germ dimension at arbitrary
    a in 3.4.8(11), p. 333.
    The empty germ remains explicit. *)
Theorem analytic_critical_centre_depth_drop (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n.+1->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n.+1->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (A:set X) (f:X->R^o) (D:X->Hom X R^o) a:
  A a ->
  @is_finite_analytic_variety R X (inner_norm hB) (inner_norm_real_norm hB) A
    [set x|A x /\ forall v,D x v = 0] ->
  (forall x,A x ->has_norm_differential (inner_norm hB) (fun z:R^o=>`|z|) A f x (D x)) ->
  ~(exists r:R,0<r /\ forall x,inner_norm hB (x-a)<r ->A x /\ f x = f a) ->
  let alpha:=@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0
    [set y|A (a+y) /\ forall v,D (a+y) v = 0] in
  alpha = @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0 \/
  (@AnalyticDepth.value R X B hB n.+1 e he omega (@AnalyticSetIdeal.value R X (inner_norm hB)
    (inner_norm_real_norm hB) 0 alpha)<n.+1)%N.
Proof.
move=>hAa hVariety hD hNotConstant alpha.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose A':set X:=[set y|A (a+y)].
pose f':X->R^o:=fun y=>f (a+y).
pose D':X->Hom X R^o:=fun y=>D (a+y).
have hA0:A' 0 by change (A (a+0));rewrite addr0.
have hVariety':@is_finite_analytic_variety R X NX hNX A'
    [set y|A' y /\ forall v,D' y v = 0].
  exact:(@finite_analytic_variety_source_translation R X NX hNX A
    [set x|A x /\ forall v,D x v = 0] a hVariety).
have hD' y (hy:A' y):has_norm_differential NX (fun z:R^o=>`|z|) A' f' y (D' y).
  have hTranslated:=@norm_differential_translate R X R^o NX (fun z:R^o=>`|z|)
    A f a y 0 (D (a+y)) (hD (a+y) hy).
  apply:(@norm_differential_domain_agreement R X R^o NX (fun z:R^o=>`|z|) hNX
    A' (fun z=>f (a+z)-0) f' y (D' y) _ hTranslated).
  by move=>z _;rewrite subr0.
have hNotConstant':~(exists r:R,0<r /\ forall y,NX y<r ->A' y /\ f' y = f' 0).
  move=>[r [hr hConstant]];apply:hNotConstant;exists r;split;first exact:hr.
  move=>x hx;have [hAx hValue]:=hConstant (x-a) hx.
  change (A (a+(x-a))) in hAx.
  change (f (a+(x-a)) = f (a+0)) in hValue.
  rewrite addrC subrK in hAx;rewrite [a+(x-a)]addrC subrK addr0 in hValue.
  by split.
exact:(@analytic_critical_germ_dimension_drop R X B hB n e he hON omega hDual
  A' f' D' hA0 hVariety' hD' hNotConstant').
Qed.
