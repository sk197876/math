(** Federer (1969), 3.2.31, pp. 268–269: fibre-threshold
    measurability and finite measure from 2.10.25–26,
    pp. 188–190. This bound is independent of rectifiability
    and includes all zero degrees and zero Lipschitz bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact LipschitzUP LipschitzBasic LipschitzFunctionCompact
  HausdorffMeasure HausdorffFibreCutoffs HausdorffFibreCost HausdorffFibreIntegralBound HausdorffFibreMeasurability
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableFunctionBorel
  TopologicalBorel PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureNonnegativeIntegral NonnegativeIntegralSetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section FiniteThreshold.
Variable R:realType.
Variables n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [finite_fibre_threshold_measurable]: supporting
    finite-mass and measurability conclusions used in Federer
    3.2.31, pp. 268–269, directly from the rough integral
    estimate and the measurable-source theorem of Chapter 2.
    The threshold uses the actual non-strict inequality and can
    include fibres of infinite mass. No rectifiability is assumed. *)
Theorem finite_fibre_threshold_measurable (F:X->Y) (W:set X) L k mu (lambda:R):
  (0<lambda)%R ->is_metric_lipschitz_bound setT F L ->
  measure_measurable (@hausdorff_measure R X (k+mu)) W ->
  @hausdorff_measure R X (k+mu) W< +oo ->
  measure_measurable (@hausdorff_measure R Y mu)
    [set y|lambda%:E<=hausdorff_fibre_mass F W k y] /\
  @hausdorff_measure R Y mu [set y|lambda%:E<=hausdorff_fibre_mass F W k y]< +oo.
Proof.
move=>hLambda hLip hW hFinite.
pose beta:=@hausdorff_measure R Y mu.
have hb:is_measure beta:=@hausdorff_measure_is_measure R Y mu.
have hX:metric_boundedly_compact X by move=>a r hr; exact (@euclidean_closed_metric_ball_compact R n a r).
have hY:metric_boundedly_compact Y by move=>a r hr; exact (@euclidean_closed_metric_ball_compact R v a r).
have hMeas:=(@hausdorff_fibre_measurability_proper_source R X Y F L W k mu hX hLip hW hFinite).1.
pose f:=hausdorff_fibre_mass F W k.
pose Z:set Y:=[set y|lambda%:E<=f y].
have hZ:measure_measurable beta Z.
  have hRay:@borel_set (extended_real_line R) [set z|lambda%:E<=z].
    apply:closed_borel_set; exact:order_closed_upper_ray_closed.
  have hPre:=@measurable_function_borel_preimage R Y (extended_real_line R) beta hb
    (partial_function_total f) hMeas [set z|lambda%:E<=z] hRay.
  by rewrite partial_function_total_preimage in hPre.
have hPos y:0<=f y.
  exact (@measure_nonnegative R X (@hausdorff_measure R X k) (@hausdorff_measure_is_measure R X k)
    (W `&` F @^-1` [set y])).
have hp:measure_almost_everywhere beta (partial_extended_nonnegative_locus (partial_function_total f)).
  apply:(measure_almost_everywhere_mono hb _ (measure_almost_everywhere_true hb))=>y _.
  exists (f y); split=>//; exact:hPos.
have [hi hi0]:=nonnegative_measurable_function_integral hb hMeas hp.
have [P [hP hPBound]]:=metric_lipschitz_of_bound hLip.
have hRough:=@hausdorff_positive_lipschitz_fibre_integral_bound R X Y F P k mu W
  hPBound hP (or_intror hY).
have hValue:=measure_upper_integral_unique (measure_upper_integral_specification beta _) hi.2.1.
rewrite hValue in hRough.
have hCoefficient:0<=(@hausdorff_fibre_bound_constant R k mu P)%:E.
  rewrite lee_fin; exact (@hausdorff_fibre_bound_constant_nonnegative R k mu P (ltW hP)).
have hBudget:(@hausdorff_fibre_bound_constant R k mu P)%:E*@hausdorff_measure R X (k+mu) W< +oo.
  apply:lte_mul_pinfty=>//.
have hMarkov:=@nonnegative_integral_arbitrary_set_bound R Y beta hb f Z lambda
  (measure_lower_integral beta (partial_function_total f)) hPos hLambda (fun y hy=>hy) hi.
have hMassFinite:lambda%:E*beta Z< +oo:=le_lt_trans hMarkov (le_lt_trans hRough hBudget).
split; first exact hZ.
change (is_true (beta Z< +oo)).
case hMass:(beta Z)=>[s| |]; [exact:ltry| |by []].
by move:hMassFinite; rewrite hMass gt0_muley ?lte_fin // ltxx.
Qed.
End FiniteThreshold.
