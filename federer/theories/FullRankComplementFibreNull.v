(** Federer (1969), 3.2.15, p. 252, final
    displayed assertion: the part of each fibre
    outside full target rank has zero complementary
    Hausdorff measure for almost every target point.
    Derive this from the proved critical and null-source
    cases of 3.2.11, retaining target dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LipschitzUP EuclideanLipschitzClassZero EuclideanLebesgueDimensions
  CoordinateInverseCoverUP CoareaRankLoci BorelCriticalCoarea CriticalCoareaJacobianZero
  CoareaCriticalFibreNull CoareaNullSourceAgreement CoareaJacobianMeasure
  Rademacher HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_rank_complement_fibres_almost_null]:
    the final display of Federer 3.2.15, p. 252.
    Both the critical differential locus and the null
    nondifferentiability locus are discharged from Lipschitzness;
    no extra differentiability premise is imposed. *)
Theorem full_rank_complement_fibres_almost_null (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  (n<m)%N -> is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y | @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
      (m-n) (mapping_fibre f (~` surjective_differential_locus f) y)=0].
Proof.
move=> hnm hf.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose mu := @euclidean_lebesgue_measure R n.
pose hm := euclidean_lebesgue_is_measure R n.
pose phi := @hausdorff_measure R X (m-n).
pose hp := @hausdorff_measure_is_measure R X (m-n).
pose C : set X := critical_target_differential_locus f.
pose D : set X := [set x | norm_differentiable_at
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n)) setT f x].
have hCB := critical_target_differential_locus_borel (euclidean_lipschitz_norm_class_zero hf).
have hI := borel_critical_coarea hnm hf hCB (fun x hx => hx).
have hZero := @critical_coarea_jacobian_measure_zero R m n f C (fun x hx => hx).
change (euclidean_coarea_measure f C=0) in hZero.
rewrite hZero in hI.
have hCnull := coarea_zero_fibre_integral_almost_null hI.
have hNnull : measure_almost_everywhere mu
    [set y | phi (mapping_fibre f (~` D) y)=0].
  apply: (coarea_null_source_fibres_zero (ltnW hnm) hf _).
  exact: federer_3_1_6 hf.
have hBoth := measure_almost_everywhere_and hm hCnull hNnull.
apply: (@measure_almost_everywhere_mono R _ mu hm _ _ _ hBoth)=> y [hyC hyN].
apply: (@measure_null_subset R X phi hp _
  (mapping_fibre f C y `|` mapping_fibre f (~` D) y)).
- move=> x [hx hfx].
  case: (pselect (D x))=> [hd|hd].
  + have [hrank|hcrit] := (ordinary_target_rank_split f x).1 hd.
    * exfalso; exact: hx hrank.
    * left; by split.
  + right; by split.
- exact (@measure_null_union R X phi hp
    (mapping_fibre f C y) (mapping_fibre f (~` D) y) hyC hyN).
Qed.
