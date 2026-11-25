(** Federer (1969), 3.4.11, p. 338:
    the actual leading ideal has no greater depth
    than the original analytic germ. A positive Haar
    witness in its proved conull tail and the
    original finite-minimum law give the full inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  InnerMetric HomInner HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing SetGermUP GermVanishingSealed AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticVarietyGermUP AnalyticInitialIdealSealed AnalyticInitialIdealTailAlmost
  MeasureUP MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_ideal_depth_bound]: the
    original ideal-depth comparison underlying the dimension
    assertion of 3.4.11, p. 338. This
    includes reducible nonempty germs and dimension zero;
    no generic prime-ideal dimension theorem is assumed. *)
Theorem analytic_initial_ideal_depth_bound (R:realType) n
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0):
  let X:=R_n R n in
  let B:=@euclidean_inner_product R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let e:=@coordinate_basis R n in
  let he:=@coordinate_basisP R n in
  let omega:=dual_basis he in
  let I:=@AnalyticSetIdeal.value R X NX hNX 0 alpha in
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 set0 ->
  (@AnalyticDepth.value R X B hB n e he omega (@AnalyticInitialIdeal.value R X NX hNX I)<=
    @AnalyticDepth.value R X B hB n e he omega I)%N.
Proof.
move=>X B hB NX hNX e he omega I hAnalytic hNonempty.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n e he mulO invO unitO hO.
have hAlmost:=@analytic_initial_ideal_tail_almost R n mulO invO unitO hO alpha theta hAnalytic hNonempty hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
have hMass:theta setT<>0%E.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R)=0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [g [_ hAll]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
apply:(analytic_reduction_depth_minimal (@AnalyticDepth.laws R X B hB n e he omega
  (@AnalyticInitialIdeal.value R X NX hNX I))).
by exists g.
Qed.
