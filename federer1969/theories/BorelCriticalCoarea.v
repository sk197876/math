(** Federer (1969), 3.2.11, p. 249: extend
    the finite critical-source conclusion to arbitrary Borel
    source mass. Countable Borel partitioning preserves exact
    fibre mass; target dimension zero is dealt with directly. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions TopologicalBorel BorelPartition BorelRegularMeasureUP
  EuclideanFiniteBorelPartition CoareaRankLoci CriticalCoareaJacobianZero FiniteCriticalCoarea
  CoareaJacobianMeasure EuclideanLinearJacobian HausdorffMeasure HausdorffClosedCoverAgreement MappingMultiplicity FibreBorelPartitionMass
  NonnegativeSum NonnegativeSumSupport TotalCountableNonnegativeIntegral LipschitzUP
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureAlmostUP MeasureAlmostBasic MeasureConullZeroIntegral PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_critical_coarea]: the critical case
    of Federer 3.2.11, p. 249, for all
    Borel source sets, including infinite mass and target
    dimension zero. Both sides of coarea are zero. *)
Theorem borel_critical_coarea (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<m)%N ->is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=`critical_target_differential_locus f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hA hCritical.
have hZero:=critical_coarea_jacobian_measure_zero hCritical.
rewrite hZero.
case:n f hnm hf hA hCritical hZero=>[|n] f hnm hf hA hCritical hZero.
- have hEmpty:A=set0.
    apply/seteqP; split=>x; last by [].
    move=>hx; have [D [_ hZ]]:=hCritical x hx.
    rewrite euclidean_linear_jacobian_zero_degree in hZ.
    by move:(oner_neq0 R); rewrite hZ eqxx.
  apply:(measure_almost_zero_integral (euclidean_lebesgue_is_measure R 0)).
  apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R 0) setT _ _
    (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R 0)))=>y _.
  change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
    (m-0) (mapping_fibre f A y)=0).
  have hFibre:mapping_fibre f A y=set0 by rewrite hEmpty; apply/seteqP; split=>x; [by move=>[[]]|by []].
  rewrite hFibre; exact (measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-0))).
- pose X:=inner_metric_space (@euclidean_inner_productP R m).
  pose Y:=inner_metric_space (@euclidean_inner_productP R n.+1).
  pose beta:=@hausdorff_measure R X (m-n.+1).
  pose hb:=@hausdorff_measure_is_measure R X (m-n.+1).
  have [H [hH hFinite]]:=euclidean_finite_borel_partition_exists hA.
  have hSub B:H B ->B `<=` A.
    move=>hB x hx; rewrite -(borel_partition_union hH); by exists B.
  have hPiece B:H B ->is_measure_integral (@euclidean_lebesgue_measure R n.+1)
      (partial_function_total (fun y=>(beta (mapping_fibre f B y):extended_real_line R))) 0.
    move=>hB.
    apply:(finite_borel_critical_coarea hnm hf (borel_partition_members hH hB) (hFinite B hB)).
    move=>x hx; exact (hCritical x (hSub B hB x hx)).
  have hFibreMeas B:H B ->measure_measurable beta B.
    move=>hB; exact (borel_regular_borel_measurable hb (@hausdorff_measure_borel_regular R X (m-n.+1))
      (borel_partition_members hH hB)).
  have hSum:=@total_countable_nonnegative_integral R [the choiceType of Y] [the choiceType of set X]
    (@euclidean_lebesgue_measure R n.+1) (euclidean_lebesgue_is_measure R n.+1) H
    (fun B y=>(beta (mapping_fibre f B y):extended_real_line R)) (fun _=>0)
    (borel_partition_countable hH) (fun B hB y=>measure_nonnegative hb _) hPiece.
  have hSumZero:@nonnegative_sum R [the choiceType of set X] H (fun _=>0)=0.
    apply:nonnegative_sum_zero=>B hB; reflexivity.
  rewrite hSumZero in hSum.
  apply:(measure_integral_graph_equivalent _ hSum)=>y r.
  change (nonnegative_sum H (fun B=>beta (mapping_fibre f B y))=r <->beta (mapping_fibre f A y)=r).
  by rewrite -(@borel_partition_fibre_mass_sum R [the topologicalType of X] (R_n R n.+1)
    beta hb f A H hH hFibreMeas y).
Qed.
