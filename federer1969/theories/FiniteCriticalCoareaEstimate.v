(** Federer (1969), 3.2.11, p. 249: the complete
    finite critical-source perturbation estimate. Apply the proved
    full-rank coarea theorem to g on A times the unit ball,
    then the actual slicing/Fubini comparison and cancel alpha(n).
    Erratum p. 5, book p. 249 line 21: source mass is L^m(A). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBlockLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanBallVolume EuclideanClosedBallVolume MetricClosedBalls TopologicalBorel
  CoareaPerturbationMap CoareaPerturbationDifferential CoareaCylinderFibres CoareaCylinderMeasure
  CoareaJacobianMeasure FullRankBorelCoarea CoareaPerturbationComparison
  CriticalPerturbationIntegralBound CoareaProjectionFibreBound HausdorffFibreCost
  HausdorffMeasure MappingMultiplicity EuclideanLinearJacobian CoordinateInverseCoverUP
  NormDifferentialUP LipschitzUP MeasureUP MeasureIntegralUP PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_critical_coarea_estimate]: the two
    estimates on p. 249 in Federer 3.2.11,
    including the corrected L^m(A) source factor. All
    differential, rank and slicing estimates are discharged;
    the original fibre integral is bounded by a finite
    constant times epsilon (L+epsilon)^(n-1) L^m(A). *)
Theorem finite_critical_coarea_estimate (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n.+1)) L e A (a:R):
  (n.+1<m)%N ->is_metric_lipschitz setT f ->is_metric_lipschitz_bound setT f L ->(0<e)%R ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  euclidean_lebesgue_measure m A< +oo ->(0<=a)%R ->
  (forall x,A x ->exists D:Hom (R_n R m) (R_n R n.+1),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n.+1)) setT f x D /\
    euclidean_linear_jacobian n.+1 D=0%R) ->
  is_measure_integral (@euclidean_lebesgue_measure R n.+1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n.+1) (mapping_fibre f A y)
        :extended_real_line R))) a%:E ->
  (a<=hausdorff_fibre_bound_constant (m-n.+1) n.+1 1 *
    (e*(L+e)^+n)*fine (euclidean_lebesgue_measure m A))%R.
Proof.
move=>hnm hf hL he hA hFin ha hCritical hI.
pose Y:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose P:=inner_metric_space (@euclidean_inner_productP R (m+n.+1)).
pose B:=@metric_closed_ball R Y ((0:R_n R n.+1)%R) (1:R).
pose Q:=coarea_cylinder A B.
pose g:=fun w:P=>(coarea_perturbation_map f e w:Y).
have hB:borel_set B:=closed_borel_set (@metric_closed_ball_closed R Y ((0:R_n R n.+1)%R) 1%R).
have hBMeas:=euclidean_borel_measurable hB.
have hAMeas:=euclidean_borel_measurable hA.
have hQBorel:=coarea_cylinder_borel hA hB.
have hQMeas:=euclidean_borel_measurable hQBorel.
have hG:is_metric_lipschitz setT g:=coarea_perturbation_map_lipschitz hf (ltW he).
have hmPos:(0<m)%N:=leq_ltn_trans (leq0n n.+1) hnm.
have hBig:(n.+1<m+n.+1)%N by rewrite -{1}(add0n n.+1) ltn_add2r.
have hRank:Q `<=`surjective_differential_locus g.
  move=>w hw.
  apply:(coarea_perturbation_full_rank (lt0r_neq0 he)).
  have [D [hD _]]:=hCritical (@euclidean_first_block R m n.+1 w) hw.1.
  by exists D.
have hCoarea:=full_rank_borel_coarea hBig hG hQBorel hRank.
rewrite addnK in hCoarea.
have haE:0<=a%:E by rewrite lee_fin.
have hCompare:=coarea_perturbation_integral_comparison (ltnW hnm) hBMeas haE hI hCoarea.
have hSource:=critical_perturbation_source_integral_bound hf hL he hQMeas hCritical.
pose K:=hausdorff_fibre_bound_constant (m-n.+1) n.+1 (1:R).
have hK:(0<K)%R:=coarea_projection_fibre_coefficient_positive R (m-n.+1) n.+1.
have hKE:0<=K%:E by rewrite lee_fin; exact:ltW hK.
have hSecond:K%:E*euclidean_coarea_measure g Q<=K%:E*
    (e*(L+e)^+n)%R%:E*euclidean_lebesgue_measure (m+n.+1) Q.
  rewrite -muleA; apply:lee_pmul; [exact hKE|exact (@measure_nonnegative R [the choiceType of P] (euclidean_coarea_measure g) (euclidean_coarea_measure_is_measure hG) Q)|exact:lexx|exact hSource].
have hBoth:=le_trans hCompare hSecond.
have hBMass:euclidean_lebesgue_measure n.+1 B=(euclidean_unit_ball_volume R n.+1)%:E.
  by rewrite /B euclidean_closed_ball_normalized_volume // expr1n mulr1.
have hMassFin:euclidean_lebesgue_measure m A \is a fin_num.
  rewrite ge0_fin_numE //; exact (@measure_nonnegative R _ _ (euclidean_lebesgue_is_measure R m) A).
rewrite (coarea_cylinder_lebesgue_mass hAMeas hBMeas) hBMass -(fineK hMassFin)
  -!EFinM lee_fin in hBoth.
have hArrange:(K*(e*(L+e)^+n)*(fine (euclidean_lebesgue_measure m A)*euclidean_unit_ball_volume R n.+1)=
    (K*(e*(L+e)^+n)*fine (euclidean_lebesgue_measure m A))*euclidean_unit_ball_volume R n.+1)%R by ring.
rewrite hArrange in hBoth.
move:hBoth; by rewrite (ler_pM2r (euclidean_unit_ball_volumeE R n.+1).2).
Qed.
