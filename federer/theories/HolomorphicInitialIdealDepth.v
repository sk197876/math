(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.11, p. 338:
    the actual leading ideal has no greater depth
    than the original holomorphic germ. A positive Haar
    witness in its proved conull tail and the
    original finite-minimum law give the full inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import UnitaryGroupHaar FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  InnerMetric HomInner HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing SetGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicVarietyGermUP HolomorphicInitialIdealSealed HolomorphicInitialIdealTailAlmost
  MeasureUP MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_ideal_depth_bound]: the
    original ideal-depth comparison underlying the dimension
    assertion of 3.4.11, p. 338. This
    includes reducible nonempty germs and dimension zero;
    no generic prime-ideal dimension theorem is assumed. *)
Theorem holomorphic_initial_ideal_depth_bound (R:realType) n
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0):
  let X:=coordinate_space (ComplexScalars.C R) n in
  let B:=@standard_hermitian_product R n in
  let hB:=@standard_hermitian_productP R n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let e:=@coordinate_basis (ComplexScalars.C R) n in
  let he:=@coordinate_basisP (ComplexScalars.C R) n in
  let omega:=dual_basis he in
  let I:=@HolomorphicSetIdeal.value R X NX hNX 0 alpha in
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 set0 ->
  (@HolomorphicDepth.value R X B hB n e he omega (@HolomorphicInitialIdeal.value R X NX hNX I)<=
    @HolomorphicDepth.value R X B hB n e he omega I)%N.
Proof.
move=>X B hB NX hNX e he omega I hHolomorphic hNonempty.
pose eR:=ordered_real_basis e;pose heR:=ordered_real_basisP he.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal [theta hTheta]]]]]]]]]]:=
  @unitary_group_haar_exists R X B hB (n+n) eR heR.
have hAlmost:=@holomorphic_initial_ideal_tail_almost R n mulO invO unitO hO
  mulU invU unitU hU alpha theta hHolomorphic hNonempty hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
have hMass:theta setT<>0%E.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R)=0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [g [_ hAll]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
apply:(analytic_reduction_depth_minimal (@HolomorphicDepth.laws R X B hB n e he omega
  (@HolomorphicInitialIdeal.value R X NX hNX I))).
by exists g.
Qed.
