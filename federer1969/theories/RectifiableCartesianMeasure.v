(** Federer (1969), 3.2.23, p. 260: the complete equality
    of restricted product measures. Compact injective chart pairs
    implement the countable decomposition, both omitted products are
    null, and the entire local measure identities glue on every subset. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianBorel RectifiableSetUP
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableCompactCharts
  RectifiableFiniteHausdorffMass RectifiableCartesianRemainders CompactChartProductMeasure
  HausdorffMeasure HausdorffClosedCoverAgreement EuclideanLebesgueHaar
  MeasureUP MeasureRestriction MeasurePushforward MeasureDisjointLocalAgreement
  BorelRegularMeasureUP BorelRegularRestriction BorelRegularHomeomorphicPushforward
  TopologicalBorel ProductBorelRectangles ProductBorelRegularity ProductMeasure
  FiniteBorelProductRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_cartesian_measure_from_charts]: supporting
    final gluing argument in Federer 3.2.23, p. 260. Compact
    charts refine 3.2.4. Both null omitted products are retained.
    Local full-measure identities and countable additivity on arbitrary
    restrictions prove equality of the whole outer measures. *)
Theorem rectifiable_cartesian_measure_from_charts (R:realType) (m mu n v:nat) (lambda:R)
    (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (C:nat->set (R_n R mu))
    (psi:nat->R_n R m->R_n R n) (gamma:nat->R_n R mu->R_n R v):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) Z ->
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  measure_pushforward (@euclidean_block_split R n v)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
      (euclidean_cartesian_set W Z))=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z).
Proof.
move=>hW hWBorel hZ hZBorel hSource hTarget.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose T:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose H:=@hausdorff_measure R X m.
pose J:=@hausdorff_measure R Y mu.
pose L:=@hausdorff_measure R T (m+mu).
have hH:=@hausdorff_measure_is_measure R X m.
have hJ:=@hausdorff_measure_is_measure R Y mu.
have hL:=@hausdorff_measure_is_measure R T (m+mu).
pose alpha:=measure_restrict H W.
pose beta:=measure_restrict J Z.
have hAlpha:=measure_restrict_is_measure hH W.
have hBeta:=measure_restrict_is_measure hJ Z.
pose nu:=product_measure hAlpha hBeta.
have hNu:=product_measure_is_measure hAlpha hBeta.
pose sigma:=measure_pushforward (@euclidean_block_split R n v)
  (measure_restrict L (euclidean_cartesian_set W Z)).
have hSigma:=measure_pushforward_is_measure (@euclidean_block_split R n v)
  (measure_restrict_is_measure hL (euclidean_cartesian_set W Z)).
have hAlphaRegular:=borel_regular_restrict_borel hH (@hausdorff_measure_borel_regular R X m) hWBorel.
have hBetaRegular:=borel_regular_restrict_borel hJ (@hausdorff_measure_borel_regular R Y mu) hZBorel.
have hRestrictedRegular:=borel_regular_restrict_borel hL (@hausdorff_measure_borel_regular R T (m+mu))
  (euclidean_cartesian_borel hWBorel hZBorel).
have hSigmaRegular:=borel_regular_homeomorphic_pushforward
  (measure_restrict_is_measure hL (euclidean_cartesian_set W Z))
  (@euclidean_block_splitK R n v) (@euclidean_block_joinK R n v)
  (@euclidean_block_split_continuous R n v) (@euclidean_block_join_continuous R n v) hRestrictedRegular.
have [U hU]:=euclidean_countable_open_base R n.
have [V hV]:=euclidean_countable_open_base R v.
have hNuRegular:=product_measure_borel_regular hAlpha hBeta hU hV hAlphaRegular hBetaRegular.
have hAlphaFinite:alpha setT< +oo.
  rewrite /alpha /measure_restrict setIT; exact:rectifiable_finite_hausdorff_mass hW.
have hBetaFinite:beta setT< +oo by rewrite /beta /measure_restrict setIT; exact hZ.2.
pose P:=fun i=>psi i @` K i.
pose Q:=fun j=>gamma j @` C j.
pose Index:=(nat*nat)%type.
pose F:=fun p:Index=>(P p.1) `*` (Q p.2).
have hPBorel i:@borel_set (inner_metric_space (@euclidean_inner_productP R n)) (P i).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X)
    (uniform_compact_chart_image_compact (hSource.1 i).1))).
have hQBorel j:@borel_set (inner_metric_space (@euclidean_inner_productP R v)) (Q j).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R Y)
    (uniform_compact_chart_image_compact (hTarget.1 j).1))).
have hFBorel p:@borel_set [the topologicalType of (X*Y)%type] (F p):=borel_product_rectangle (hPBorel p.1) (hQBorel p.2).
have hMeas p (_:@setT Index p):measure_measurable sigma (F p) /\measure_measurable nu (F p).
  split.
  - exact:(borel_regular_borel_measurable hSigma hSigmaRegular (hFBorel p)).
  - exact:(borel_regular_borel_measurable hNu hNuRegular (hFBorel p)).
have hDisjoint p q (hp:@setT Index p) (hq:@setT Index q):p!=q ->
    forall x,F p x ->F q x ->False.
  clear hp hq; case:p=>i j; case:q=>k l; move=>hDifferent [x y] [hPi hQj] [hPk hQl].
  have [hI|hI]:=eqVneq i k.
  - have hJL:j!=l.
      apply/negP=>/eqP hJL; move:hDifferent; by rewrite hI hJL eqxx.
    exact:(hTarget.2.1 j l hJL y hQj hQl).
  - exact:(hSource.2.1 i k hI x hPi hPk).
have hSigmaNull:sigma (~` (\bigcup_(p in @setT Index) F p))=0.
  have hNull:=rectifiable_cartesian_chart_remainder_null hW hZ hSource hTarget.
  have hBadSet:(euclidean_cartesian_set W Z) `&`
      ((@euclidean_block_split R n v) @^-1` (~` (\bigcup_(p in @setT Index) F p)))=
      euclidean_cartesian_set W Z `\`
        (\bigcup_(p in @setT Index) euclidean_cartesian_set (P p.1) (Q p.2)).
    apply/seteqP; split.
    - move=>w [hw hn]; split; first exact hw.
      move=>[p hp hwp]; apply:hn; by exists p.
    - move=>w [hw hn]; split; first exact hw.
      move=>[p hp hwp]; apply:hn; by exists p.
  change (L ((euclidean_cartesian_set W Z) `&`
    ((@euclidean_block_split R n v) @^-1` (~` (\bigcup_(p in @setT Index) F p))))=0).
  rewrite hBadSet; exact hNull.
have hNuNull:nu (~` (\bigcup_(p in @setT Index) F p))=0.
  have hProofBridge:=product_measure_factors_equal hAlpha
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) W)
    hBeta (measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) Z)
    (erefl alpha) (erefl beta).
  rewrite /nu hProofBridge.
  exact:(rectifiable_cartesian_reference_remainder_null hSource hTarget).
have hLocal p (hp:@setT Index p):measure_restrict sigma (F p)=measure_restrict nu (F p).
  clear hp; case:p=>i j.
  have hSigmaPiece:measure_restrict sigma (F (i,j))=
      measure_pushforward (@euclidean_block_split R n v)
        (measure_restrict L (euclidean_cartesian_set (P i) (Q j))).
    apply:funext=>S; rewrite /sigma /measure_pushforward /measure_restrict.
    congr (L _); apply/seteqP; split.
    - by move=>w [_ [hp hs]]; split.
    - move=>w [hp hs]; split.
      + split; [exact:((hSource.1 i).2 _ hp.1)|exact:((hTarget.1 j).2 _ hp.2)].
      + by split.
  have hProduct:=compact_chart_product_measure (hSource.1 i).1 (hTarget.1 j).1.
  have hNuPiece:=@finite_borel_product_rectangle_restriction R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) alpha beta hAlpha hBeta U V (P i) (Q j)
    hU hV hAlphaRegular hBetaRegular hAlphaFinite hBetaFinite (hPBorel i) (hQBorel j).
  have hAlphaPiece:=@measure_restrict_nested_subset R [the choiceType of X] H W (P i) (hSource.1 i).2.
  have hBetaPiece:=@measure_restrict_nested_subset R [the choiceType of Y] J Z (Q j) (hTarget.1 j).2.
  have hFactors:=product_measure_factors_equal
    (measure_restrict_is_measure hAlpha (P i))
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) (P i))
    (measure_restrict_is_measure hBeta (Q j))
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) (Q j))
    hAlphaPiece hBetaPiece.
  exact:(eq_trans hSigmaPiece (eq_trans hProduct (esym (eq_trans hNuPiece hFactors)))).
have hAgreement:=@measure_disjoint_local_agreement R [the choiceType of (X*Y)%type]
  [the choiceType of (Index:Type)] sigma nu hSigma hNu setT F
  (countableP setT) hMeas hDisjoint hSigmaNull hNuNull hLocal.
have hBridge:=product_measure_factors_equal hAlpha
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) W)
  hBeta (measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) Z)
  (erefl alpha) (erefl beta).
exact:(eq_trans hAgreement hBridge).
Qed.

(** Source for [rectifiable_cartesian_measure_identity]: the complete
    displayed measure equality in Federer 3.2.23, p. 260,
    under exactly the printed Borel and rectifiability hypotheses.
    The first factor is genuinely m-rectifiable. Charts, their
    inverses, differentials and all measure comparisons are proved
    internally; no selected parametrization is a final premise. *)
Theorem rectifiable_cartesian_measure_identity (R:realType) (m mu n v:nat)
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) Z ->
  measure_pushforward (@euclidean_block_split R n v)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
      (euclidean_cartesian_set W Z))=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z).
Proof.
move=>hW hWBorel hZ hZBorel.
have hRectW:=rectifiable_hausdorff_measure_rectifiable hW.
have hWMeas:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m)
  (@hausdorff_measure_borel_regular R (inner_metric_space (@euclidean_inner_productP R n)) m) hWBorel.
have hZMeas:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R v)) mu)
  (@hausdorff_measure_borel_regular R (inner_metric_space (@euclidean_inner_productP R v)) mu) hZBorel.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have [K [psi hSource]]:=@federer_3_2_18 R m n 2%R W hRectW hWMeas hTwo.
have [C [gamma hTarget]]:=@federer_3_2_18 R mu v 2%R Z hZ hZMeas hTwo.
exact:(rectifiable_cartesian_measure_from_charts hW hWBorel hZ hZBorel hSource hTarget).
Qed.
