(** Federer (1969), 3.2.13, p. 251: invariant sphere
    integration is its total mass times integration along a
    normalized Haar orbit. Apply the integral uniqueness theorem
    2.7.11(2), p. 128, as in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CovariantIntegralUP HaarIntegralUP HaarIntegralLaws CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures WeilCondition DaniellIntegralNegation DaniellSpacePushforward
  CompactSupportFunctionUP CompactSupportDaniellContinuity DaniellSpaceCompactSpace
  MonotoneDaniellIntegralUP RealIntegralFunctionalUP FiniteCompactInvariantIntegral
  MeasureUP MeasurePushforward BorelRegularMeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_finite_invariant_orbit_integral]: the
    application of 2.7.11(2), p. 128, to sphere integration
    in Federer 3.2.13, p. 251. Its generic form uses a
    finite invariant Borel measure and the actual Haar orbit
    integral. No orbit-measure identification is assumed. *)
Theorem compact_finite_invariant_orbit_integral (R:realType) (G X:topologicalType)
    (mul:G->G->G) (inv:G->G) (e:G) (A:G->X->X)
    (hG:is_locally_compact_hausdorff_group mul inv e)
    (hA:is_homogeneous_space mul A) (hX:hausdorff_space X)
    (mu:set X->\bar R) (theta:set G->\bar R) (C:R) (x:X):
  compact [set:G] ->is_measure mu ->is_borel_regular_measure mu ->0<C ->mu setT=C%:E ->
  (forall g,measure_pushforward (A g) mu=mu) ->is_normalised_haar_measure mul theta ->
  forall (u:X->R) (q:R),compactly_supported_continuous_functions u ->
    is_measure_integral theta (real_total_integrand (u\o orbit_map A x)) q%:E ->
    is_measure_integral mu (real_total_integrand u) (C*q)%:E.
Proof.
move=>hGc hm hB hC hMass hPush hTheta u q hu hq.
pose hgl:=topological_group_laws (lch_group_topological hG).
have hXC:=compact_homogeneous_space_compact hGc hA.
have hCont g:continuous (A g):=homogeneous_translation_continuous hA g.
have hInj g:injective (A g):=can_inj (homogeneous_translation_inverse_left hgl hA g).
have hFin:(mu setT < +oo)%E by rewrite hMass ltry.
have [L [hRep hInv]]:=finite_compact_invariant_integral_exists hXC hm hB hFin hCont hInj hPush.
have hL1:L (fun _=>1)=C.
  have h:=compact_representing_measure_total hXC hm hRep.
  exact:EFin_inj (eq_trans (esym h) hMass).
have [[lambda [hHaar hThetaM hThetaRep hThetaReg]] hTheta1]:=hTheta.
have hLambda1:lambda (fun _=>1)= 1.
  have h:=compact_representing_measure_total hGc hThetaM hThetaRep.
  rewrite hTheta1 in h; exact:EFin_inj (esym h).
have [hOrbitMon hOrbitCov]:=orbit_pushforward_invariant_integral hGc hA hX x hHaar.
pose nu:=daniell_pushforward (orbit_map A x) lambda.
have hNu:is_invariant_integral A nu.
  constructor; first exact:monotone_daniell_is_daniell hOrbitMon.
  exact:hOrbitCov.
have hNu1:nu (fun _=>1)= 1:=hLambda1.
have hone:=compact_space_constant_one R hXC.
have hNuNonzero:exists2 v,compactly_supported_continuous_functions v &nu v<>0.
  exists (fun _=>1)=>//; rewrite hNu1; exact/eqP/oner_neq0.
have hLNonzero:exists2 v,compactly_supported_continuous_functions v &L v<>0.
  exists (fun _=>1)=>//; rewrite hL1; exact/eqP/lt0r_neq0.
have hChiM:forall g h:G,(1:R)= 1*1 by move=>g h; rewrite mulr1.
have hChiCont:continuous (fun _:G=>(1:real_line_metric R)) by move=>g; exact:cvg_cst.
have [c [hc hMultiple]]:=covariant_integral_unique_multiple x hG hA hX hChiM
  (fun _=>oner_neq0 R) hChiCont hNu hInv hNuNonzero hLNonzero.
have hcC:c=C.
  have h:=hMultiple _ hone; rewrite hL1 hNu1 mulr1 in h; exact:esym h.
have hOrbitK:=compactly_supported_compose (orbit_map_continuous hA x)
  (compact_homogeneous_orbit_proper hGc hA (x:=x) hX) hu.
have hValue:=EFin_inj (measure_integral_unique (hThetaRep _ hOrbitK) hq).
have hLValue:L u=C*q.
  rewrite (hMultiple u hu) hcC /nu /daniell_pushforward hValue.
  by [].
by rewrite -hLValue; exact:hRep u hu.
Qed.
