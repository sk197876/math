(** Federer (1969), 3.2.22, pp. 259–260:
    glue Borel chart-pair approximations of the intrinsic
    Jacobian while retaining both null remainders. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  NormMetricScaleContinuity TopologicalBorel BorelFunctionUP BorelDisjointFunctionGluing
  DisjointFunctionGluingUP DisjointFunctionGluing
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure MeasureApproximateJacobian
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts
  RectifiableChartPairPieces RectifiableChartPairFamily CompactRectifiableChartPairs RectifiableChartPairBorelJacobianWeight
  RectifiableNullTargetJacobian RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_borel_jacobian_approximation]:
    justify the implicit intrinsic-Jacobian measurability
    in Federer 3.2.22, pp. 259–260.
    For each lambda>1 glue the local nonnegative Borel
    weights on disjoint compact P_ij. They approximate
    the original intrinsic mu-Jacobian within lambda^mu
    and its inverse almost everywhere on W. The zero
    value outside the pairs is valid above Q by 3.2.21;
    source R is null by the erratum p. 5 correction
    to book p. 258 lines 20/22. Only existing opaque
    gluing laws are used; J0 need not be measurable. *)
Theorem rectifiable_borel_jacobian_approximation (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  1<lambda ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  exists h:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R,
    is_borel_function h /\ (forall w,0<=h w) /\
    (forall w,~W w ->h w=0) /\
    measure_almost_everywhere_on (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
        (lambda^+mu)^-1*J0 w<=h w /\ h w<=lambda^+mu*J0 w].
Proof.
move=>hLambda hRectW hW hRectZ hZ hF hRange hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
have hr:=@hausdorff_measure_is_measure R X m.
have [K [psi hSource]]:=@federer_3_2_18 R m n lambda W hRectW hW hLambda.
have [C [gamma hTarget]]:=@federer_3_2_18 R mu v lambda Z hRectZ hZ hLambda.
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
pose SrcR:=W `\` (\bigcup_i psi i @` K i).
pose TarQ:=Z `\` (\bigcup_j gamma j @` C j).
have hLocal (p:nat*nat):exists h:X->real_line_metric R,
    is_borel_function h /\ (forall w,0<=h w) /\
    measure_almost_everywhere_on rho (P p) [set w|
      (lambda^+mu)^-1*J0 w<=h w /\ h w<=lambda^+mu*J0 w].
  exact:(rectifiable_chart_pair_borel_jacobian_weight hLambda (hSource.1 p.1).1
    (hTarget.1 p.2).1 (hSource.1 p.1).2 hW hRectW.2 hF hJ0).
have [h hLaws]:=choice hLocal.
have hFCont:continuous F.
  have [L [hL hB]]:=hF; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
have hPBorel (p:nat*nat):@borel_set X (P p).
  have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hSource.1 p.1).1).
  have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hTarget.1 p.2).1).
  have hPsiCont:continuous (psi p.1:inner_metric_space (@euclidean_inner_productP R m)->X).
    have [L [hL hB]]:=hPsi; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
    exact:(hB.2 a b Logic.I Logic.I).
  have hGammaCont:continuous (gamma p.2:inner_metric_space (@euclidean_inner_productP R mu)->Y).
    have [L [hL hB]]:=hGamma; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
    exact:(hB.2 a b Logic.I Logic.I).
  have hCompact:=compact_rectifiable_chart_pair_piece
    (rectifiable_chart_compact (hSource.1 p.1).1) (rectifiable_chart_compact (hTarget.1 p.2).1)
    hPsiCont hFCont hGammaCont.
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X) hCompact)).
have hDisjoint:forall p q,@setT (nat*nat) p ->setT q ->p<>q ->P p `&` P q=set0.
  move=>p q _ _ hPQ; exact:(@rectifiable_chart_pair_pieces_disjoint R m n mu v lambda W Z K psi C gamma F hSource hTarget p q hPQ).
pose g:=@disjoint_function_gluing R X (nat*nat)%type setT P h hDisjoint.
have hGlue:=@disjoint_function_gluing_specification R X (nat*nat)%type setT P h hDisjoint.
have hCount:countable (@setT (nat*nat)) by exact:countableP.
pose Index:=(nat*nat)%type.
exists g; split.
- exact:(@borel_disjoint_function_gluing R X [the choiceType of (Index:Type)] setT P h g
    hCount (fun p _=>hPBorel p) (fun p _=>(hLaws p).1) hGlue).
split; first exact:(nonnegative_disjoint_function_gluing (fun p w _ _=>(hLaws p).2.1 w) hGlue).
split.
- move=>w hNotW; apply:(hGlue.2 w)=>[[p _ hp]].
  exact:(hNotW ((hSource.1 p.1).2 w hp.1)).
have hPairAE p:measure_almost_everywhere rho [set w|P p w ->
    (lambda^+mu)^-1*J0 w<=g w /\ g w<=lambda^+mu*J0 w].
  apply:(measure_almost_everywhere_mono hr _
    ((measure_almost_everywhere_on_implication _ _ _).1 (hLaws p).2.2))=>w hp hw.
  change ((lambda^+mu)^-1*J0 w<=g w /\ g w<=lambda^+mu*J0 w).
  have hg:g w=h p w:=hGlue.1 p w Logic.I hw.
  rewrite hg; exact:(hp hw).
have hPairs:=@measure_almost_everywhere_countable R [the choiceType of X]
  [the choiceType of (Index:Type)] rho hr setT _ hCount (fun p _=>hPairAE p).
have hZero:=@rectifiable_null_target_jacobian_zero R m n v mu W F TarQ J0
  hRectW hW hF hTarget.2.2 hJ0.
have hNotR:measure_almost_everywhere rho (~`SrcR).
  rewrite /measure_almost_everywhere setCK; exact hSource.2.2.
have hAll:=measure_almost_everywhere_and hr hPairs
  (measure_almost_everywhere_and hr ((measure_almost_everywhere_on_implication _ _ _).1 hZero) hNotR).
have hDecomposition:=rectifiable_chart_pair_remainder_cover hSource hTarget hRange.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hr _ hAll)=>w [hEvery [hZeroW hOutside]] hw.
have hCoverW:=hw; rewrite hDecomposition in hCoverW.
have [[[hw0 hQ]|[p _ hp]]|hR]:=hCoverW.
- change ((lambda^+mu)^-1*J0 w<=g w /\ g w<=lambda^+mu*J0 w).
  have hg0:g w=0.
    apply:(hGlue.2 w)=>[[p _ hP]].
    apply:hQ.2; exists p.2; first exact:Logic.I; exact hP.2.
  by rewrite hg0 (hZeroW (conj hw hQ)) !mulr0.
- exact:(hEvery p Logic.I hp).
- by exfalso; exact:(hOutside hR).
Qed.
