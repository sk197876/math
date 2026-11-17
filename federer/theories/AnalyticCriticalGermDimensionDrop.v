(** Federer (1969), 3.4.8(11), p. 333:
    the germ of the actual critical
    variety has dimension below the ambient
    dimension whenever the function is not
    locally constant. Reuse the generic rank-zero
    theorem, ideal separation and original (7). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies NormDifferentialUP AnalyticGermRing SetGermUP
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP GermVanishingSealed GermVanishingIdeal AnalyticIdealPropriety
  AnalyticDepthSealed AnalyticNonzeroIdealDepth AnalyticProperVarietyNonzeroIdeal CriticalGermLocalConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_critical_germ_dimension_drop]:
    the critical variety H has smaller
    dimension in 3.4.8(11), p. 333.
    The empty germ is explicit because
    the original dimension is defined only
    on nonempty variety germs. *)
Theorem analytic_critical_germ_dimension_drop (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n.+1->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n.+1->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (A:set X) (f:X->R^o) (D:X->Hom X R^o):
  A 0 ->
  @is_finite_analytic_variety R X (inner_norm hB) (inner_norm_real_norm hB) A
    [set x|A x /\ forall v,D x v = 0] ->
  (forall x,A x ->has_norm_differential (inner_norm hB) (fun z:R^o=>`|z|) A f x (D x)) ->
  ~ (exists r:R,0<r /\ forall x,inner_norm hB x<r ->A x /\ f x = f 0) ->
  let alpha:=@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0
    [set x|A x /\ forall v,D x v = 0] in
  alpha = @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0 \/
  (@AnalyticDepth.value R X B hB n.+1 e he omega (@AnalyticSetIdeal.value R X (inner_norm hB)
    (inner_norm_real_norm hB) 0 alpha)<n.+1)%N.
Proof.
move=>hA0 hVariety hD hNotConstant alpha.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose H:set X:=[set x|A x /\ forall v,D x v = 0].
have hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
  exists A,H;split;first exact:hA0.
  by split.
case:(pselect (alpha = @set_germ T 0 set0))=>hEmpty;first by left.
right.
have hNotWhole:alpha<>@set_germ T 0 setT.
  move=>hWhole;apply:hNotConstant.
  have [r [hr hConstant]]:=@critical_whole_germ_locally_constant R X R^o NX (fun z:R^o=>`|z|)
    hNX (@scalar_absolute_value_norm R) A f D 0 hD hWhole.
  exists r;split;first exact:hr.
  move=>x hx;apply:hConstant;by rewrite subr0.
have [beta [hBeta hNonzero]]:=@analytic_proper_variety_nonzero_ideal R X NX hNX 0 alpha hAlpha hNotWhole.
apply:(@analytic_nonzero_proper_ideal_depth_lt R X B hB n e he hON omega hDual
  (@AnalyticSetIdeal.value R X NX hNX 0 alpha)).
- exact:analytic_set_ideal_ring_laws.
- move=>hUnit;apply:hEmpty;exact:(analytic_set_ideal_contains_one alpha).1 hUnit.
- by exists beta.
Qed.
