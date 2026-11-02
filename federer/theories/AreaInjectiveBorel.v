(** Federer (1969), 3.2.3, p. 243: the area
    formula on the injective differentiability locus, by the
    Borel cover of 3.2.2, subordinate partition, summation
    and the limit as lambda decreases to one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormMetricScaleContinuity NormClassZeroWhole
  LipschitzUP EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  TopologicalBorel BorelRegularMeasureUP InjectiveBorelImage BorelPartition BorelSubordinatePartition
  CountablyClosedFamilyUP MeasureUP MeasureBasic MeasureCountableAdditivity
  MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeLowerIntegral MeasureIntegralUniqueness MeasureSubsetIntegral PartialFunctionBasic
  ExtendedRealOrderTopology MappingMultiplicity NonnegativeSum NonnegativeSumScale
  InjectiveDifferentialPieceUP InjectiveDifferentialCover InnerOwnNormTopology
  EuclideanJacobianMeasurable JacobianDensityMeasure AreaPieceIntegralBounds
  PartitionMultiplicityIntegral HausdorffMeasure HausdorffClosedCoverAgreement ExtendedPowerGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_borel_partition_sum]: summing the
    Jacobian measure over H in Federer 3.2.3, p. 243,
    by countable additivity. The Borel partition's members
    are assumed measurable for the supplied measure. *)
Lemma measure_borel_partition_sum (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) A H:
  is_borel_partition A H -> (forall B,H B -> measure_measurable mu B) ->
  mu A=nonnegative_sum H (fun B=>mu B).
Proof.
move=>hH hMeas; rewrite -(borel_partition_union hH).
apply:(@measure_countable_disjoint_additivity R X [the choiceType of set X] mu hm H (fun B=>B)
  (borel_partition_countable hH) hMeas).
move=>B C hB hC hNe x hx hy.
have hn:B<>C by move=>he; by rewrite he eqxx in hNe.
have hEmpty:B `&` C=set0:=borel_partition_disjoint hH hB hC hn.
have hh:(B `&` C) x by split.
by rewrite hEmpty in hh.
Qed.

(** Source for [area_injective_borel_distortion_bounds]:
    the two lambda^(2m) comparisons after summing H in
    Federer 3.2.3, p. 243. Both integral values may
    be infinite, so this intermediate step needs no finite
    source-measure restriction. *)
Theorem area_injective_borel_distortion_bounds (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)) (lambda:R):
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=` injective_differential_locus f -> (1<lambda)%R ->
  exists b,is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f A y:extended_real_line R))) b /\
    euclidean_jacobian_measure f A<=(lambda^+(m+m)%N)%R%:E*b /\
    b<=(lambda^+(m+m)%N)%R%:E*euclidean_jacobian_measure f A.
Proof.
move=>hLip hA hALocus hl.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
have [L [hL hBound]]:=hLip.
have hCont:continuous f.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=>x y; exact (hBound.2 x y Logic.I Logic.I).
have hContNorm:continuous (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))=>
    (f x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))).
  apply:(@metric_fixed_lipschitz_continuous R _ _ _ L (ltW hL)).
  by move=>x y; exact (hBound.2 x y Logic.I Logic.I).
have hZero:=@norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f hContNorm.
have [G hG]:=injective_differential_borel_cover_exists hZero hl.
have hGB E:G E -> @borel_set X E.
  move=>hE; exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 (hG.2.2 E hE).1).
have hCover:A `<=` \bigcup_(E in G) E by rewrite hG.2.1.
have [H [hH hSub]]:=borel_countable_cover_subordinate_partition hA hG.1 hGB hCover.
have hBmu B:H B -> measure_measurable mu B.
  move=>hB; exact (borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)
    (borel_partition_members hH hB)).
have hBnu B:H B -> measure_measurable nu B.
  move=>hB; exact (euclidean_jacobian_measure_measurable hLip (hBmu B hB)).
have hBInj B:H B -> {in B &,injective f}.
  move=>hB; have [_ [E [hE hBE]]]:=hSub B hB.
  move=>x y hx hy he.
  exact ((hG.2.2 E hE).2.2.1 x y (mem_set (hBE x (set_mem hx)))
    (mem_set (hBE y (set_mem hy))) he).
have hImage B:H B -> measure_measurable beta (f @` B).
  move=>hB.
  have hIB:=@injective_borel_image_borel R X Y f B (@euclidean_metric_complete R m)
    (@euclidean_metric_separable R m) (@metric_hausdorff R Y) hCont (borel_partition_members hH hB).
  have hImB:borel_set (f @` B).
    apply:hIB=>x y hx hy he; exact (hBInj B hB x y (mem_set hx) (mem_set hy) he).
  exact (borel_regular_borel_measurable hb (@hausdorff_measure_borel_regular R Y m) hImB).
have hLocal B:H B -> nu B<=(lambda^+(m+m)%N)%R%:E*beta (f @` B) /\
    beta (f @` B)<=(lambda^+(m+m)%N)%R%:E*nu B.
  move=>hB; have [_ [E [hE hBE]]]:=hSub B hB.
  have [a [ha hBounds]]:=area_piece_integral_bounds hLip hl (hG.2.2 E hE) (hBmu B hB) hBE.
  have hnuI:=euclidean_jacobian_measure_integral hLip (hBmu B hB).
  have heq:a=nu B:=measure_integral_unique ha hnuI.
  by rewrite -heq.
have hSum:nu A=nonnegative_sum H (fun B=>nu B):=measure_borel_partition_sum hn hH hBnu.
pose b:=nonnegative_sum H (fun B=>beta (f @` B)).
have hInt:is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R))) b.
  exact (partition_univalent_multiplicity_integral hb hH hBInj hImage).
have hCoeff:(0<=lambda^+(m+m)%N)%R by apply:exprn_ge0; exact (ltW (lt_trans ltr01 hl)).
exists b; split; first exact hInt.
split.
- change (is_true (nu A<=(lambda^+(m+m)%N)%R%:E*b)).
  rewrite hSum /b -nonnegative_sum_scale; last 2 first.
  + exact hCoeff.
  + move=>B hB; exact (measure_nonnegative hb _).
  apply:nonnegative_sum_mono=>B hB; exact (hLocal B hB).1.
- change (is_true (b<=(lambda^+(m+m)%N)%R%:E*nu A)).
  rewrite hSum /b -nonnegative_sum_scale; last 2 first.
  + exact hCoeff.
  + move=>B hB; exact (measure_nonnegative hn _).
  apply:nonnegative_sum_mono=>B hB; exact (hLocal B hB).2.
Qed.

(** Source for [area_formula_injective_borel]: the first
    case of Federer 3.2.3(1), p. 243. The two
    lambda^(2m) bounds force exact equality of the Jacobian
    and multiplicity integrals. Infinite masses are included. *)
Theorem area_formula_injective_borel (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=` injective_differential_locus f ->
  is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f A y:extended_real_line R)))
    (euclidean_jacobian_measure f A).
Proof.
move=>hLip hA hALocus.
have [b [hInt hBounds]]:=area_injective_borel_distortion_bounds hLip hA hALocus (ltr1n R 2).
pose beta:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hnu:=euclidean_jacobian_measure_is_measure hLip.
have hb:0<=b.
  pose Y:=inner_metric_space (@euclidean_inner_productP R n).
  pose F:=partial_function_total (fun y=>(@mapping_multiplicity R _ Y f A y:extended_real_line R)).
  pose hbeta:=@hausdorff_measure_is_measure R Y m.
  have hPos:measure_almost_everywhere beta (partial_extended_nonnegative_locus F).
    apply:(@measure_almost_everywhere_mono R Y beta hbeta setT _ _
      (measure_almost_everywhere_true hbeta))=>y _.
    exists (@mapping_multiplicity R _ Y f A y); split; first by [].
    exact:mapping_multiplicity_nonnegative.
  have he:=@measure_lower_integral_unique R Y beta F _ b
    (measure_lower_integral_specification beta F) hInt.2.2.
  rewrite -he; exact (measure_lower_integral_nonnegative hbeta hPos).
have hBoth lambda:(1<lambda)%R ->
    euclidean_jacobian_measure f A<=(lambda^+(m+m)%N)%R%:E*b /\
    b<=(lambda^+(m+m)%N)%R%:E*euclidean_jacobian_measure f A.
  move=>hl; have [c [hIc hc]]:=area_injective_borel_distortion_bounds hLip hA hALocus hl.
  have he:c=b:=measure_integral_unique hIc hInt.
  by rewrite -he.
have h1:euclidean_jacobian_measure f A<=b.
  exact (@extended_power_geometric_squeeze R b _ (m+m)%N hb (fun l hl=>(hBoth l hl).1)).
have h2:b<=euclidean_jacobian_measure f A.
  exact (@extended_power_geometric_squeeze R _ b (m+m)%N (measure_nonnegative hnu A)
    (fun l hl=>(hBoth l hl).2)).
have he:b=euclidean_jacobian_measure f A by apply/eqP; rewrite eq_le h2 h1.
by rewrite -he.
Qed.
