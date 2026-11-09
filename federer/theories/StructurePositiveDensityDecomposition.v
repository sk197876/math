(** Federer (1969), 3.3.15, p. 299: the complete positive
    upper-density decomposition of the ORIGINAL finite-mass source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  OrthogonalProjectionProbability StructureConeUP StructureFiniteSourceRegularisation
  StructureDensityStrata StructureDensityRectifiableParts MetricDensities
  RectifiableSetUP RectifiableElementary CountablyRectifiableUnions PureUnrectifiableLaws
  PureUnrectifiableCountableUnions MeasureUP MeasureBasic MeasureRestriction
  MeasureFiniteClosure MeasureCountableClosure MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext BorelRegularMeasureUP TopologicalBorel MeasurableBorelFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_15]: COMPLETE Federer 3.3.15, p. 299.
    The original W has finite phi outer mass and positive upper
    m density of phi restricted to W at phi almost every point
    of W. There exists a phi measurable, countably (phi,m)
    rectifiable Q whose ORIGINAL remainder W minus Q is purely
    (phi,m) unrectifiable and projects to a Lebesgue null set at
    almost every original projection. Original W need not be
    measurable; upper densities may be infinite. The actual finite
    regularisation, original density strata and contained Borel
    rectifiable parts are proved and remain local. No finite mass
    for Q, null hull difference, or supplied decomposition is assumed. *)
Theorem federer_3_3_15 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->phi W< +oo ->
  measure_almost_everywhere_on phi W
    [set a|0<upper_metric_density m (measure_restrict phi W) a] ->
  exists Q,is_countably_measure_m_rectifiable phi m Q /\measure_measurable phi Q /\
    is_purely_measure_m_unrectifiable phi m (W `\` Q) /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (W `\` Q))=0].
Proof.
move=>hStructure hFinite hPositive.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [psi [hReg [hClass [hRadon [hTotal [hValue [hDomination hDensity]]]]]]]:=
  @structure_finite_source_regularisation R n m phi W hStructure hFinite.
have hPsi:is_measure psi:=derivation_measure_law hClass.
have hRegular:is_borel_regular_measure psi:=derivation_measure_borel_regular hClass.
have hPsiFinite:psi setT< +oo by rewrite hTotal.
pose E i:=structure_upper_density_stratum m psi i.
have hParts i:=@structure_density_rectifiable_part R n m hmn psi i hPsi hRegular hPsiFinite.
have [B hB]:=choice hParts.
pose S:=\bigcup_i B i.
pose F:=W `\` \bigcup_i E i.
pose Q:=F `|` S.
have hFNull:phi F=0.
  have hLocus:(\bigcup_i E i)=[set a|0<upper_metric_density m (measure_restrict phi W) a].
    rewrite /E structure_density_strata_union.
    apply/seteqP; split=>a /=; by rewrite hDensity.
  by rewrite /F hLocus.
have hPhiBorel C:borel_set C ->measure_measurable phi C.
  apply:(@open_measurable_implies_borel_measurable R [the topologicalType of X] phi hStructure.1).
  move=>U hU.
  have hClosed:=hStructure.2 _ (open_closedC hU).
  have hOpen:=measure_measurable_complement hClosed; by rewrite setCK in hOpen.
have hSMeasurable:measure_measurable phi S.
  rewrite /S.
  exact (@measure_measurable_countable_union R [the choiceType of X] [the choiceType of (nat:Type)]
    phi hStructure.1 setT B (countableP setT) (fun i _=>hPhiBorel (B i) (hB i).2.1)).
have hSRectifiable:is_countably_m_rectifiable m S.
  rewrite /S.
  apply:(@countably_rectifiable_countable_union R [the metricType R of X]
    [the choiceType of (nat:Type)] m setT B (countableP setT)).
  move=>i _; exact:(hB i).2.2.1.
have hQRectifiable:is_countably_measure_m_rectifiable phi m Q.
  split; first exact:hStructure.1.
  exists S; split; first exact:hSRectifiable.
  apply:(@measure_null_subset R [the choiceType of X] phi hStructure.1 (Q `\` S) F _ hFNull).
  by move=>x [[hx|hx] hn]; [exact:hx|exfalso; exact:hn hx].
have hQMeasurable:measure_measurable phi Q.
  exact:(measure_measurable_union hStructure.1 (measure_null_measurable hStructure.1 hFNull) hSMeasurable).
pose C i:=W `&` (E i `\` B i).
have hPureC i:is_purely_measure_m_unrectifiable phi m (C i).
  have hPurePsi:is_purely_measure_m_unrectifiable psi m (C i).
    apply:(@pure_unrectifiable_subset R [the metricType R of X] psi m (E i `\` B i) (C i) _ (hB i).2.2.2.1).
    by move=>x [_ hx].
  apply:(@pure_unrectifiable_dominated_on_source R [the metricType R of X] m phi psi (C i) hStructure.1 hPurePsi).
  move=>D hD.
  have hWD:W `&` D=D.
    apply/seteqP; split=>x; first by move=>[_ hx].
    move=>hx; split; [exact:(hD x hx).1|exact:hx].
  have hBound:=hDomination D; by rewrite hWD in hBound.
have hCover:W `\` Q `<=` \bigcup_i C i.
  move=>x [hx hnQ].
  have hUnion:(\bigcup_i E i) x.
    apply:contrapT=>hn; apply:hnQ; left; by split.
  have [i _ hi]:=hUnion; exists i; first exact:Logic.I.
  split; first exact:hx.
  split; first exact:hi.
  move=>hBi; apply:hnQ; right; by exists i.
have hPureUnion:is_purely_measure_m_unrectifiable phi m (\bigcup_i C i).
  apply:(@pure_unrectifiable_countable_union R [the metricType R of X] m phi
    [the choiceType of (nat:Type)] setT C hStructure.1 (countableP setT)).
  by move=>i _; exact:hPureC.
have hPure:is_purely_measure_m_unrectifiable phi m (W `\` Q):=
  @pure_unrectifiable_subset R [the metricType R of X] phi m _ _ hCover hPureUnion.
have hTheta:=theta_star_is_measure R hmn.
have hAll:measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    (\bigcap_i [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (E i `\` B i))=0]).
  apply:(@measure_almost_everywhere_countable R _ [the choiceType of (nat:Type)] _ hTheta setT _ (countableP setT)).
  move=>i _; exact:(hB i).2.2.2.2.
exists Q; split; first exact:hQRectifiable.
split; first exact:hQMeasurable.
split; first exact:hPure.
apply:(measure_almost_everywhere_mono hTheta _ hAll)=>p hp.
have hLeb:=euclidean_lebesgue_is_measure R m.
pose G i:=euclidean_projection_linear p @` (E i `\` B i).
have hNull:euclidean_lebesgue_measure m (\bigcup_i G i)=0.
  apply:(@measure_null_countable_union R _ [the choiceType of (nat:Type)] _ hLeb setT G (countableP setT)).
  move=>i _; exact:hp i Logic.I.
apply:(@measure_null_subset R _ _ hLeb _ _ _ hNull).
move=>y [x hx <-].
have [i _ [hWx hEi]]:=hCover x hx.
exists i; first exact:Logic.I.
by exists x.
Qed.
