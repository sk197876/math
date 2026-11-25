(** Federer (1969), 3.4.8(13), p. 336:
    the variety of the original rotated ideal is
    represented by the inverse image of the original
    analytic variety. Apply the existing vanishing-ideal
    transport and analytic variety recovery theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure NormFiniteLinearBound
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticVarietyGermUP
  AnalyticVarietyGermSeparation FiniteAnalyticVarietyUP FiniteAnalyticLinearPullback
  IdealVarietyGermUP IdealVarietyGermSealed IdealVarietyGermExistence
  AnalyticRotatedGermIdeal AnalyticRotatedVanishingIdeal AnalyticRotatedIdealRecovery.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_variety_representative]: the
    original identity between var(I_g) and the rotated
    germ of alpha in 3.4.8(13), p. 336.
    All coordinate maps act on the original centre. *)
Theorem analytic_rotated_variety_representative (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (I:set [the comNzRingType of (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)])
    (hI:is_finitely_generated_commutative_ideal I)
    (g:@orthogonal_group R X B hB n e he)
    (hIg:is_finitely_generated_commutative_ideal (@analytic_rotated_germ_ideal R X B hB n e he I g))
    (U H:set X):
  U 0 ->@is_finite_analytic_variety R X (inner_norm hB) (inner_norm_real_norm hB) U H ->
  I=@AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
    (@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 H) ->
  @IdealVarietyGerm.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
    (@analytic_rotated_germ_ideal R X B hB n e he I g) hIg =
  @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0
    ((@orthogonal_element_map R X B hB n e he g) @^-1` H).
Proof.
move=>hU0 hH hIEquation.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose u:=@orthogonal_element_map R X B hB n e he g.
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
pose alpha:=@IdealVarietyGerm.value R X NX hNX 0 Ig hIg.
have hOriginal:=@given_vanishing_ideal_variety_recovery R X NX hNX 0 I hI
  (@set_germ T 0 H) hIEquation.
have hRecovered:=@analytic_rotated_ideal_variety_recovery R X B hB n e he I g hI hIg hOriginal.
have hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 Ig alpha (@IdealVarietyGerm.laws R X NX hNX 0 Ig hIg)).
have hBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he u.
have hPreimage:@is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0 (u @^-1` H)).
  exists (u @^-1` U),(u @^-1` H);split;first by rewrite /= linear0.
  split;last exact:erefl.
  exact:finite_analytic_linear_pullback hBound hH.
apply:(analytic_variety_germ_ideal_injective hAlpha hPreimage).
rewrite -hRecovered hIEquation.
exact:analytic_rotated_vanishing_ideal.
Qed.
