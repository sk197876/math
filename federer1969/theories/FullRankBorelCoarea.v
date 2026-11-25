(** Federer (1969), 3.2.11, p. 249: the full-rank
    case. Cover the actual surjective-differential locus with
    3.2.9, refine to a Borel partition, apply 3.2.10
    to each member and sum. No finite-mass assumption is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLipschitzClassZero CoordinateInverseCoverUP CoordinateInverseCover
  CoordinateCoarea CoareaJacobianMeasure EuclideanTargetJacobianMeasurable
  HausdorffMeasure HausdorffClosedCoverAgreement MappingMultiplicity FibreBorelPartitionMass
  LipschitzUP TopologicalBorel BorelPartition BorelSubordinatePartition BorelRegularMeasureUP
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral PartialFunctionUP PartialFunctionBasic NonnegativeSum AreaInjectiveBorel
  ExtendedRealOrderTopology TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_rank_borel_coarea]: the first case
    in the proof of Federer 3.2.11, p. 249.
    Every point of the Borel source set has an actual
    surjective differential. The proof sums the printed local
    formulas and permits arbitrary, possibly infinite source mass. *)
Theorem full_rank_borel_coarea (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  (n<m)%N ->is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=` surjective_differential_locus f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hA hRank.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R X (m-n).
pose nu:=euclidean_coarea_measure f.
have hn:=euclidean_coarea_measure_is_measure hf.
have [G [hCount [hCover hPieces]]]:=coordinate_inverse_cover_class_zero (euclidean_lipschitz_norm_class_zero hf).
have hGB E:G E ->@borel_set [the topologicalType of X] E.
  move=>hE; exact (hPieces E hE).1.
have hCov:A `<=` \bigcup_(E in G) E.
  move=>x hx; exact (hCover x (hRank x hx)).
have [H [hH hSub]]:=borel_countable_cover_subordinate_partition hA hCount hGB hCov.
have hMeas B:H B ->measure_measurable (@euclidean_lebesgue_measure R m) B.
  move=>hB; exact (euclidean_borel_measurable (borel_partition_members hH hB)).
have hNuMeas B:H B ->measure_measurable nu B.
  move=>hB; exact (euclidean_coarea_measure_measurable hf (hMeas B hB)).
have hFibreMeas B:H B ->measure_measurable beta B.
  move=>hB; exact (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X (m-n))
    (@hausdorff_measure_borel_regular R X (m-n)) (borel_partition_members hH hB)).
have hPieceIntegral B (hB:H B):is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(beta (mapping_fibre f B y):extended_real_line R))) (nu B).
  have [_ [E [hEG hBE]]]:=hSub B hB.
  have [a [hSource hTarget]]:=federer_3_2_10 hnm hf (hPieces E hEG) (hMeas B hB) hBE.
  have hValue:=measure_integral_unique hSource (euclidean_coarea_measure_integral hf (hMeas B hB)).
  by rewrite hValue in hTarget.
have hSum:=@total_countable_nonnegative_integral R [the choiceType of Y] [the choiceType of set X]
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) H
  (fun B y=>(beta (mapping_fibre f B y):extended_real_line R)) nu (borel_partition_countable hH)
  (fun B hB y=>measure_nonnegative (@hausdorff_measure_is_measure R X (m-n)) _) hPieceIntegral.
rewrite -(measure_borel_partition_sum hn hH hNuMeas) in hSum.
apply:(@measure_integral_graph_equivalent R _ _ _ _ _ _ hSum)=>y r.
change (nonnegative_sum H (fun B=>beta (mapping_fibre f B y))=r <->beta (mapping_fibre f A y)=r).
by rewrite -(@borel_partition_fibre_mass_sum R [the topologicalType of X] (R_n R n) beta
  (@hausdorff_measure_is_measure R X (m-n)) f A H hH hFibreMeas y).
Qed.
