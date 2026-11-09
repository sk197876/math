(** Federer (1969), 3.3.16, p. 299: actual replacement
    measures agree with Hausdorff measure on arbitrary subsets of
    countably rectifiable carriers, without a supplied finite mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureReplacementMeasureUP
  CountablyRectifiableBorelEnlargement RectifiableSetUP RectifiableElementary
  BorelPartition BorelSubordinatePartition TopologicalBorel HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostDisjointSum NonnegativeSumSupport BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_rectifiable_measure_agreement]: supporting
    3.2.26/countable-partition passage in Federer 3.3.16, p. 299.
    Close the ORIGINAL bounded-image family, form its Borel
    subordinate partition, and restrict BOTH original measures by
    the original arbitrary A before summing. Every intersection
    remains a subset of an actual bounded rectifiable image.
    Infinite carrier mass and nonmeasurable A are retained; no
    universal Hausdorff/Gross comparison is asserted. *)
Theorem countably_rectifiable_measure_agreement (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_measure phi ->is_borel_regular_measure phi ->
  (forall F,is_m_rectifiable m F ->phi F=@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m F) ->
  is_countably_m_rectifiable m S ->A `<=` S ->
  phi A=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
move=>hPhi hRegular hAgreement hS hAS.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hHRegular:is_borel_regular_measure H:=@hausdorff_measure_borel_regular R [the metricType R of X] m.
have [G [hG [hClosed hCover]]]:=countably_rectifiable_closed_family_enlargement hS.
pose U:=\bigcup_(F in G) F.
have hU:borel_set U.
  apply:borel_set_countable_union hG _=>F hF; exact:closed_borel_set (hClosed F hF).1.
have hAU:A `<=` U by move=>x hx; exact:hCover x (hAS x hx).
have [P [hP hSubordinate]]:=@borel_countable_cover_subordinate_partition [the topologicalType of X]
  U G hU hG (fun F hF=>closed_borel_set (hClosed F hF).1) (fun x hx=>hx).
pose mu:=measure_restrict phi A.
pose nu:=measure_restrict H A.
have hMu:is_measure mu:=measure_restrict_is_measure hPhi A.
have hNu:is_measure nu:=measure_restrict_is_measure hH A.
have hLocal B:P B ->mu B=nu B.
  move=>hB; have [hBU [F [hFG hBF]]]:=hSubordinate B hB.
  apply:hAgreement.
  apply:(@rectifiable_subset R [the metricType R of X] m F (A `&` B) _ (hClosed F hFG).2).
  by move=>x [_ hx]; exact:hBF x hx.
have hDisjoint B C:P B ->P C ->B!=C ->forall x,B x ->C x ->False.
  move=>hB hC /eqP hNe x hx hy.
  have hEmpty:=borel_partition_disjoint hP hB hC hNe.
  have hBoth:(B `&` C) x by split.
  by rewrite hEmpty in hBoth.
have hNull (rho:set X->\bar R):is_measure rho ->
    measure_restrict rho A (setT `\` (\bigcup_(B in P) B))=0.
  move=>hRho; rewrite (borel_partition_union hP) /measure_restrict.
  have hEmpty:A `&` (setT `\` U)=set0.
    apply/seteqP; split=>x; last by case.
    by move=>[hx [_ hn]]; exact:hn (hAU x hx).
  rewrite hEmpty; exact:measure_empty hRho.
have hSumPhi:=@measure_almost_disjoint_cover_sum R [the choiceType of X]
  [the choiceType of set X] mu hMu setT P id (borel_partition_countable hP)
  (fun _ _ _ _=>Logic.I) hDisjoint
  (fun B hB=>@measure_restrict_measurable R [the choiceType of X] phi A B
    (borel_regular_borel_measurable hPhi hRegular (borel_partition_members hP hB)))
  (hNull phi hPhi).
have hSumH:=@measure_almost_disjoint_cover_sum R [the choiceType of X]
  [the choiceType of set X] nu hNu setT P id (borel_partition_countable hP)
  (fun _ _ _ _=>Logic.I) hDisjoint
  (fun B hB=>@measure_restrict_measurable R [the choiceType of X] H A B
    (borel_regular_borel_measurable hH hHRegular (borel_partition_members hP hB)))
  (hNull H hH).
rewrite /mu /measure_restrict setIT in hSumPhi.
rewrite /nu /measure_restrict setIT in hSumH.
change (phi A=H A).
rewrite hSumPhi hSumH; apply:nonnegative_sum_ext=>B hB.
exact:hLocal B hB.
Qed.

(** Source for [structure_replacement_carrier_agreement]: the
    replacement-measure instance of the proved countable carrier
    agreement in Federer 3.3.16, p. 299. Use only independent
    measure, Borel regularity and original bounded-image laws. *)
Lemma structure_replacement_carrier_agreement (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_replacement_measure m phi ->is_countably_m_rectifiable m S ->A `<=` S ->
  phi A=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
move=>hLaws.
exact:(@countably_rectifiable_measure_agreement R n m phi A S
  (structure_replacement_measure_law hLaws) (structure_replacement_borel_regular hLaws)
  (structure_replacement_rectifiable_agreement hLaws)).
Qed.
