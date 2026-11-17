(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    pp. 328–329: original A_p membership implies original B_p
    after Haar almost every original unitary prefix rotation. The
    actual positive jet, exact coordinate chart, sphere measure and
    arbitrary original Haar normalization are proved internally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import FieldPrefixCoordinateLaws HolomorphicGermRepresentatives HolomorphicInitialIdealSealed HolomorphicNormalizedJetPolynomial HolomorphicInitialPolynomialUP HolomorphicInitialPolynomialGermUP HolomorphicInitialRotatedIdeal PointedHolomorphicInitialPolynomialGerm HolomorphicInitialPolynomialLaws HolomorphicHomogeneousGermDirection PolynomialFunctions StandardHermitian Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition PointedHolomorphicLinearPullbackForms
  HolomorphicCoordinateSubringFamilySealed UnitaryCoordinateFixing HolomorphicUnitaryPrefixInvariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import ComplexScalarLaws CommutativeIdealUP GrassmannAbbreviations EuclideanInnerProduct ComplexModulus ComplexScalarNorm ContinuousMultilinearSealed OrthonormalFamilies FiniteCoordinates HolomorphicCoordinateNorm
  StandardHermitianCoordinates ComplexEuclideanCoordinates HolomorphicGermJetsSealed HolomorphicGermFormsUP
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicReductionPrefixWitness
  HolomorphicGermCoordinateDirections HolomorphicPrefixSphereCoordinates HolomorphicReductionDirectionalTransport
  FieldPrefixCoordinatesSealed HolomorphicCoordinateSubringFamilyUP HolomorphicPrefixGermSubring
  MetricSubsetBackground HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic HaarIntegralUP
  UnitaryFixingSphereAction UnitaryFixingSphereHaarNull.
Section Fibre.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable hON:orthonormal_family H e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable I:set G.
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable j:'I_n.
Local Notation p:=((j:nat).+1).
Local Notation hPN:=(ltn_ord j).
Local Notation aIndex:=(@Ordinal n.+1 p (ltn_ord j)).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) p).
Local Notation NY:=(@holomorphic_coordinate_norm R p).
Local Notation hNY:=(@holomorphic_coordinate_norm_laws R p).
Local Notation hNYR:=(complex_norm_real hNY).
Local Notation projection:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega p hPN).
Local Notation inclusion:=(@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e p hPN).
Local Notation hProjection:=(@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega p hPN).
Local Notation hInclusion:=(@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e p hPN).
Local Notation K:=(@HolomorphicInitialIdeal.value R X NX hNXR I).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega p hPN).
Local Notation J:=([set i:'I_n|(p<=i)%N]).
Local Notation F:=(@holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e p).
Local Notation sphere:=(@unitary_fixing_sphere R X H hH n e J).
Local Notation MS:=([the metricType R of metric_subset sphere]).
Local Notation SR:=(@holomorphic_prefix_real_sphere_inclusion R X p inclusion).
Local Notation PR:=(@holomorphic_prefix_real_sphere_projection R X p projection).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.
Variables (mulF:F->F->F) (invF:F->F) (unitF:F).
Variable hF:is_subgroup_restriction mulU invU unitU F mulF invF unitF.

(** Source for [holomorphic_initial_ideal_haar_fibre]: the
    complete original complex A_p-to-almost-B_p assertion, prescribed
    by 3.4.12, p. 339. No exceptional-direction or Haar
    comparison conclusion is supplied as a premise. *)
Theorem holomorphic_initial_ideal_haar_fibre (mu:set F->\bar R) (g:U):
  is_left_haar_measure mulF mu ->
  @holomorphic_reduction_actual_A R X H hH n e he omega I aIndex g ->
  measure_almost_everywhere mu
    [set h:F|@holomorphic_reduction_actual_B R X H hH n e he omega K j (mulU g (set_val h))].
Proof.
move=>hMu hA.
have [beta [hRotated [hBeta [k [hPositive [hTop hLower]]]]]]:=
  @holomorphic_reduction_prefix_witness R X H hH n e he omega I aIndex g hI hProper hA.
have [Q [hQPolynomial [hQHOL hQFormula]]]:=
  @holomorphic_normalized_jet_polynomial_exists R Y (@standard_hermitian_product R p)
    (@standard_hermitian_productP R p) p (@coordinate_basis (ComplexScalars.C R) p)
    (@coordinate_basisP (ComplexScalars.C R) p) k beta.
pose f:@holomorphic_representative_type R Y NY hNYR 0:=exist _ (fun x:Y=>Q x)
  (ex_intro _ setT (conj Logic.I hQHOL)).
pose pi:=holomorphic_germ f.
have hInitial:is_initial_holomorphic_germ_polynomial beta k Q.
  by split;last split;last split.
have hPolynomialGerm:HolomorphicInitialPolynomialGermUP.is_initial_polynomial_germ beta pi.
  exists k,Q,f;split;first exact:hInitial.
  by split.
have hProjectionOnto y:exists x,projection x=y.
  exists (inclusion y).
  exact:(@field_prefix_projection_section (ComplexScalars.C R) X n e omega p hPN
    projection inclusion hDual hProjection hInclusion).
have hPullInitial:=@pointed_holomorphic_initial_polynomial_germ R X Y NX NY hNXR hNYR projection E
  (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega p hPN)
  hProjectionOnto beta pi hPolynomialGerm.
have hRotatedK:@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR K g (E pi).
  apply:(@holomorphic_initial_rotated_ideal_member R X H hH n e he I g (E beta) (E pi)).
  - have hBounds:(ltn_ord aIndex:is_true (p<=n)%N)=hPN:=@bool_irrelevance (p<=n)%N (ltn_ord aIndex) hPN.
    by rewrite hBounds in hRotated.
  - exact:hPullInitial.
pose diagonal:=fun y:Y=>@ContinuousMultilinear.evaluation R k
  (restricted_space (ComplexScalars.embed R) Y)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY (@complex_modulus R) hNYR
  (@complex_modulus_real_norm R) [ffun _:'I_k=>y] (@HolomorphicGermJets.value R Y NY hNYR 0 k beta).
have hOnto:forall y:Y,exists v,@complex_from_real_coordinate_hom R p v=y.
  move=>y;exists (complex_real_coordinates y);change (complex_from_real_coordinates (complex_real_coordinates y)=y).
  exact:complex_real_coordinatesK.
have [_ hSphereNull]:=@holomorphic_germ_coordinate_exceptional_directions_null R Y NY hNYR 0 k beta
  (p+p) (@complex_from_real_coordinate_hom R p) hOnto hTop.
pose D:=fun v:R_n R (p+p)=>diagonal (complex_from_real_coordinates v)=0.
have hNull:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (p+p))) (p+p-1)
    [set v|inner_norm (@euclidean_inner_productP R (p+p)) v= 1 /\D v]=0%:E.
  have hSame:[set v:R_n R (p+p)|inner_norm (@euclidean_inner_productP R (p+p)) v= 1 /\D v]=
      [set v:R_n R (p+p)|D v /\inner_norm (@euclidean_inner_productP R (p+p)) v= 1].
    by apply/seteqP;split=>v [h1 h2];split.
  rewrite hSame;exact:hSphereNull.
have hAxis:sphere (e j).
  split.
  - apply:inner_norm_value;first exact:ler01.
    by rewrite expr1n /hermitian_real_part hON eqxx -(rmorph1 (ComplexScalars.embed R)) ComplexScalarTheory.re_embed.
  - move=>i hi;change (is_true ((j:nat)<(i:nat))%N) in hi;rewrite hON.
    have hDifferent:j!=i.
      apply/eqP=>hEqual;by rewrite -hEqual ltnn in hi.
    by rewrite (negbTE hDifferent).
pose u:MS:=exist _ (e j) (mem_set hAxis).
have hDoublePositive:(0<p+p)%N by rewrite addn_gt0 ltn0Sn.
have hOrbitNull:=@unitary_fixing_sphere_haar_coordinate_null R X H hH (n+n) eR heR n e J
  mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF (p+p) hDoublePositive SR PR
  (@holomorphic_prefix_real_sphere_section R X n e omega hDual p hPN projection inclusion hProjection hInclusion)
  (@holomorphic_prefix_real_sphere_distance R X H hH n e hON p hPN inclusion hInclusion)
  (@holomorphic_prefix_real_sphere_image R X H hH n e he hON omega hDual p hPN projection inclusion hProjection hInclusion)
  mu u D hMu hNull.
have hBadSet:[set h:F|D (PR (val (@unitary_fixing_sphere_action R X H hH (n+n) eR heR n e J h u)))]=
    [set h:F|diagonal (projection (mapg (set_val h) (e j)))=0].
  have hValue h:complex_from_real_coordinates
      (PR (val (@unitary_fixing_sphere_action R X H hH (n+n) eR heR n e J h u)))=
      projection (mapg (set_val h) (e j)).
    change (complex_from_real_coordinates (complex_real_coordinates (projection (mapg (set_val h) (e j))))=
      projection (mapg (set_val h) (e j))).
    exact:complex_real_coordinatesK.
  apply:funext=>h.
  change ((diagonal (complex_from_real_coordinates
    (PR (val (@unitary_fixing_sphere_action R X H hH (n+n) eR heR n e J h u))))=0)=
    (diagonal (projection (mapg (set_val h) (e j)))=0)).
  exact:(congr1 (fun y:Y=>diagonal y=0) (hValue h)).
rewrite hBadSet in hOrbitNull.
pose Good:set F:=[set h|diagonal (projection (mapg (set_val h) (e j)))<>0].
have hAlmost:measure_almost_everywhere mu Good.
  rewrite /measure_almost_everywhere.
  have hComplement:~` Good=[set h:F|diagonal (projection (mapg (set_val h) (e j)))=0].
    apply/seteqP;split=>h.
    - move=>hNot;apply:contrapT=>hNonzero;exact:hNot hNonzero.
    - move=>hZero hGood;exact:hGood hZero.
  rewrite hComplement;exact:hOrbitNull.
have [lambda [hLambda hMeasure hRep hRegular]]:=hMu.
apply:(@measure_almost_everywhere_mono R (Choice.clone F _) mu hMeasure Good
  [set h:F|@holomorphic_reduction_actual_B R X H hH n e he omega K j (mulU g (set_val h))]
  _ hAlmost)=>h hGood.
have hQ:@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega p (E pi).
  rewrite (holomorphic_coordinate_subring_family_member
    (@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega) hPN).
  apply/holomorphic_prefix_germ_subring_membership;by exists pi.
have hQNonzero:Q (projection (mapg (set_val h) (e j)))<>0.
  rewrite hQFormula.
  move=>hZero;apply:hGood.
  have hFactorial:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  have hBack:=congr1 (fun z:restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o=>
    ((k`!)%:R:R)*:z) hZero.
  rewrite scalerA (mulfV hFactorial) scale1r scaler0 in hBack.
  exact:hBack.
have hDirectionPi:has_nonzero_holomorphic_directional_jet hNY pi
    (projection (mapg (set_val h) (e j))).
  exact:(@holomorphic_homogeneous_germ_direction R Y NY hNY f k Q _ hPositive
    (fun x=>erefl _) (holomorphic_initial_polynomial_laws hInitial).2.2.1 hQNonzero).
have hDirection:has_nonzero_holomorphic_directional_jet hNX (E pi) (mapg (set_val h) (e j)).
  have [l [hPositiveL hNonzero]]:=hDirectionPi.
  exists l;split;first exact:hPositiveL.
  rewrite (@pointed_holomorphic_linear_pullback_form_diagonal R X Y NX NY hNX hNY 0 0 projection E
    (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega p hPN)
    (@holomorphic_prefix_projection_zero R X n omega p hPN) l pi (mapg (set_val h) (e j))).
  exact:hNonzero.
refine (@holomorphic_reduction_directional_transport R X H hH n e he omega hDual K
  mulO invO unitO hO mulU invU unitU hU j g (set_val h) (E pi) _ _ hQ hDirection).
- exact:set_valP h.
- exact:hRotatedK.
Qed.
End Fibre.
