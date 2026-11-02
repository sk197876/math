(** Federer (1969), 3.2.39, p. 275: finitely
    many disjoint compact original source cores nearly attain
    the actual Jacobian measure through their image costs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes JacobianDensityMeasure EuclideanJacobianFiniteMass
  EuclideanJacobianImageCost LipschitzUP NormMetricScaleContinuity CompactLipschitzImageMass
  HausdorffMeasure HausdorffClosedCoverAgreement BorelImageCoverCost BorelCaratheodoryMeasure
  FiniteBorelCostApproximation FiniteCompactImageApproximation BorelClosedProjection
  MeasureUP MeasureBasic MeasureRestriction BorelRegularRestriction TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_jacobian_disjoint_core_family_exists]:
    supporting the finite-family appeal to 3.2.3, 2.10.10
    and 2.10.8 in Federer 3.2.39, p. 275. Finite
    Borel partition costs for the actual Jacobian measure are
    approximated in the original source by compact cores.
    Restrict the target Hausdorff measure to the actual compact
    image before using finite-measure compact approximation;
    ambient H^m is never assumed globally Radon or finite.
    Original disjoint Borel pieces make the compact cores
    genuinely disjoint. Their subsequent grid cover is separate. *)
Theorem compact_jacobian_disjoint_core_family_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (A:set (inner_metric_space (@euclidean_inner_productP R m))) (e:R):
  is_metric_lipschitz setT f ->compact A ->0<e ->
  exists (I:finType) (K:I->set (inner_metric_space (@euclidean_inner_productP R m))),
    (forall i,compact (K i) /\K i `<=` A) /\
    (forall i j,i!=j ->K i `&` K j=set0) /\
    (euclidean_jacobian_measure f A<=
      (\sum_i @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` K i))+e%:E)%E.
Proof.
move=>hLip hA he.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
pose c:=borel_image_cover_cost f beta.
pose nu:=euclidean_jacobian_measure f.
have hABorel:borel_set A:=closed_borel_set (compact_closed (@metric_hausdorff R X) hA).
have hAM:measure_measurable (@euclidean_lebesgue_measure R m) A:=euclidean_borel_measurable hABorel.
have hValue:nu A=borel_caratheodory_measure c A:=euclidean_jacobian_image_cost_measure hLip hABorel.
have hFinite:(borel_caratheodory_measure c A< +oo)%E.
  rewrite -hValue; exact:euclidean_jacobian_finite_source_mass hLip hAM (euclidean_compact_finite hA).
have hHalf:0<e/2 by rewrite divr_gt0 // ltr0n.
have [I [S [hS [hDisjoint hApprox]]]]:=@finite_borel_partition_cost_approximation R X c A (e/2)
  (borel_image_cover_cost_laws f hb) (@euclidean_metric_separable R m) hABorel hFinite hHalf.
rewrite -hValue in hApprox.
have hf:continuous (f:X->Y).
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L hBound.1)=>x y.
  exact:hBound.2 x y Logic.I Logic.I.
pose mu:=measure_restrict beta (f @` A).
have hm:is_measure mu:=measure_restrict_is_measure hb (f @` A).
have hImageCompact:compact (f @` A):=continuous_compact (continuous_subspaceT hf) hA.
have hImageBorel:borel_set (f @` A):=closed_borel_set (compact_closed (@metric_hausdorff R Y) hImageCompact).
have hRegular:=borel_regular_restrict_borel hb (@hausdorff_measure_borel_regular R Y m) hImageBorel.
have hMuFinite:(mu setT< +oo)%E.
  rewrite /mu /measure_restrict setIT; exact:compact_lipschitz_image_finite_hausdorff_mass hLip hA.
have [K [hK hCost]]:=@finite_continuous_compact_image_approximation R X Y I mu f S (e/2)
  (@euclidean_metric_complete R m) (@euclidean_metric_separable R m) (@metric_hausdorff R Y)
  hf hm hRegular hMuFinite (fun i=>@metric_borel_suslin R X (S i) (hS i).1) hHalf.
have hRestricted T:T `<=` A ->mu (f @` T)=beta (f @` T).
  move=>hTA; rewrite /mu /measure_restrict.
  have hEq:(f @` A) `&` (f @` T)=f @` T.
    apply/seteqP; split; first by move=>y [_ hy].
    move=>y [x hx hfx]; split; [exists x; [exact:hTA x hx|exact hfx]|by exists x].
  by rewrite hEq.
have hLeft:(\sum_i mu (f @` S i))=(\sum_i beta (f @` S i))%E.
  apply:eq_bigr=>i _; exact:hRestricted (hS i).2.
have hRight:(\sum_i mu (f @` K i))=(\sum_i beta (f @` K i))%E.
  apply:eq_bigr=>i _; apply:hRestricted=>x hx; exact:(hS i).2 x ((hK i).2 x hx).
rewrite hLeft hRight in hCost.
exists I,K; split.
- move=>i; split; first exact:(hK i).1.
  move=>x hx; exact:(hS i).2 x ((hK i).2 x hx).
split.
- move=>i j hij; apply/seteqP; split=>[x [hi hj]|x []].
  have hBoth:(S i `&` S j) x by split; [exact:(hK i).2 x hi|exact:(hK j).2 x hj].
  by rewrite (hDisjoint i j hij) in hBoth.
- have hFinal:=le_trans hApprox (leeD hCost (lexx (e/2)%R%:E)).
  have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
  have hE:e/2+e/2=e by field.
  rewrite -addeA -EFinD hE in hFinal; exact hFinal.
Qed.
