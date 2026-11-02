(** Federer (1969), 3.2.13, p. 250: the
    coarea integral for the radial norm. The
    scalar positive-ray presentation and dimension-one case
    are separate obligations; this supporting theorem applies
    the actual 3.2.12 in its printed dimension range. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanRadialDifferential
  RadialCoareaJacobian EuclideanLebesgueDimensions EuclideanWeightedCoarea CoareaFibreIntegral
  LipschitzUP PartialFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality MeasurableFunctionUP
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_coarea_integral_high_dimension]: the
    first coarea step for f(x)=|x| in Federer
    3.2.13, p. 250. It proves existence
    and equality of the source and actual fibre integrals,
    retaining all signed infinite integral values. Source
    dimensions zero and one are not claimed by this helper. *)
Lemma radial_coarea_integral_high_dimension (R:realType) m (g:R_n R m->R):
  (1<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 1)
      (coarea_fibre_integral (@euclidean_radial_norm R m) (real_total_integrand g)) a.
Proof.
move=>hm [b hg].
have hLip:is_metric_lipschitz setT (@euclidean_radial_norm R m).
  exists 1%R; split; first exact:ltr01; exact:euclidean_radial_unit_lipschitz.
have [a [hI hFibre]]:=federer_3_2_12 hm hLip (ex_intro _ b hg).
exists a; split=>//.
apply:(measure_integral_almost_equal (euclidean_lebesgue_is_measure R m) hI).
apply:radial_jacobian_density_almost_equal; first exact:ltn_trans (ltnSn 0) hm.
exact:hg.1.
Qed.
