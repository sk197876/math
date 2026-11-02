(** Federer (1969), 3.2.11, p. 249: the
    critical-rank coarea conclusion for finite Borel source mass.
    Every perturbation estimate is proved in earlier supporting
    modules, and epsilon is now removed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes TopologicalBorel
  FiniteCoareaFibreIntegral FiniteCriticalCoareaEstimate CoareaVanishingPerturbation
  CoareaProjectionFibreBound HausdorffFibreCost HausdorffMeasure MappingMultiplicity
  EuclideanLinearJacobian NormDifferentialUP LipschitzUP MeasureUP MeasureIntegralUP
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_critical_coarea]: the
    critical-set conclusion of Federer 3.2.11, p. 249.
    The right-hand fibre integral is zero, with exactly
    finite Borel source mass and actual critical differentials.
    The positive target-dimension restriction is removed separately
    by the degree-zero Jacobian normalization. *)
Theorem finite_borel_critical_coarea (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n.+1)) A:
  (n.+1<m)%N ->is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  euclidean_lebesgue_measure m A< +oo ->
  (forall x,A x ->exists D:Hom (R_n R m) (R_n R n.+1),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n.+1)) setT f x D /\
    euclidean_linear_jacobian n.+1 D=0%R) ->
  is_measure_integral (@euclidean_lebesgue_measure R n.+1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n.+1) (mapping_fibre f A y)
        :extended_real_line R))) 0.
Proof.
move=>hnm hf hA hFin hCritical.
have hAMeas:=euclidean_borel_measurable hA.
have [a [ha hI]]:=finite_coarea_fibre_integral (ltnW hnm) hf hAMeas hFin.
have [L [hL hBound]]:=hf.
pose M:=fine (euclidean_lebesgue_measure m A).
have hMassNonnegative:=measure_nonnegative (euclidean_lebesgue_is_measure R m) A.
have hMassFin:euclidean_lebesgue_measure m A \is a fin_num by rewrite ge0_fin_numE //.
have hM:(0<=M)%R by rewrite /M -lee_fin fineK.
pose K:=hausdorff_fibre_bound_constant (m-n.+1) n.+1 (1:R).
have hK:(0<=K)%R:=ltW (coarea_projection_fibre_coefficient_positive R (m-n.+1) n.+1).
have hError e:(0<e)%R ->(a<=K*(e*(L+e)^+n)*M)%R.
  move=>he; exact (finite_critical_coarea_estimate hnm hf hBound he hA hFin ha hCritical hI).
have hZero:=coarea_vanishing_perturbation ha hK hBound.1 hM hError.
by rewrite hZero in hI.
Qed.
