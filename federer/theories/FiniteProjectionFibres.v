(** Supporting the integral-geometric product assertion of Federer (1969),
    2.10.46, p. 204. A finite I_1 value gives finite projection multiplicity
    integrals almost everywhere by 2.10.15, p. 178; each finite multiplicity
    integral then gives finite fibres almost everywhere by 2.4.3(4), p. 82.
    This supplies the null-factor safeguard for Freilich (1950), Theorem
    4.5, Part 4, pp. 245–247, before rotation averaging. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions ProjectionMultiplicityIntegral MappingMultiplicity CountingMeasure
  OrthogonalProjectionProbability ProjectionBeta IntegralGeometricMeasure IntegralGeometricMultiplicity
  ExtendedRealOrderTopology PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureFiniteUpperApproximant TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_projection_integral_almost_finite_fibres]:
    supporting finite-fibre condition for 2.10.46, p. 204,
    from 2.10.10, p. 176, and 2.4.3(4),
    p. 82. A Borel set with finite multiplicity
    integral has finite projection fibres almost everywhere. *)
Theorem finite_projection_integral_almost_finite_fibres (R : realType) n k
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) :
  borel_set V -> projection_multiplicity_integral V p< +oo ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R k)
    [set y | finite_set (mapping_fibre (euclidean_projection_linear p) V y)].
Proof.
move=> hV hfin.
have hi := projection_multiplicity_integral_specification p hV.
have hv := measure_upper_integral_unique
  (measure_upper_integral_specification (@euclidean_lebesgue_measure R k) _) hi.2.1.
have hh := @finite_upper_integral_below_infinity_almost R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  (@euclidean_lebesgue_measure R k) (euclidean_lebesgue_is_measure R k)
  (projection_multiplicity_integrand V p) ltac:(by rewrite hv).
apply: (@measure_almost_everywhere_mono R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  (@euclidean_lebesgue_measure R k) (euclidean_lebesgue_is_measure R k) _ _ _ hh).
move=> y [z [hz hzfin]].
change (@mapping_multiplicity R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  (euclidean_projection_linear p) V y=z) in hz.
apply: contrapT=> hinf.
have hn := @counting_measure_infinite R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (mapping_fibre (euclidean_projection_linear p) V y) hinf.
by rewrite -hz /mapping_multiplicity hn ltxx in hzfin.
Qed.

(** Source for [finite_integral_geometric_almost_finite_projection_integrals]:
    supporting almost-everywhere condition for 2.10.46, p. 204.
    The actual averaging integral in 2.10.15, p. 178,
    has value beta_1 times I_1. A finite I_1 value
    therefore gives finite inner integrals almost everywhere.
    This does not yet prove the cylinder product identity. *)
Theorem finite_integral_geometric_almost_finite_projection_integrals (R : realType) n k
    (hkn : (k<=n)%N) (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<k)%N -> borel_set V -> @integral_geometric_measure R n k hkn 1 V< +oo ->
  measure_almost_everywhere (@orthogonal_projection_probability R n k hkn)
    [set p | projection_multiplicity_integral V p< +oo].
Proof.
move=> hk hV hfin.
have hi := (@federer_2_10_15 R n k hkn V hk hV).2.1.
have hnon := measure_nonnegative (@integral_geometric_measure_is_measure R n k hkn 1 (lexx _)) V.
have hnum : @integral_geometric_measure R n k hkn 1 V \is a fin_num.
  by rewrite (ge0_fin_numE hnon).
have hvalue : (@projection_beta R n k hkn 1)%:E*@integral_geometric_measure R n k hkn 1 V< +oo.
  by rewrite -(fineK hnum) -EFinM ltry.
have hv := measure_upper_integral_unique
  (measure_upper_integral_specification (@orthogonal_projection_probability R n k hkn) _) hi.2.1.
have hh := @finite_upper_integral_below_infinity_almost R
  (orthogonal_projection_metric_space R n k)
  (@orthogonal_projection_probability R n k hkn) (@theta_star_is_measure R n k hkn)
  (partial_function_total (projection_multiplicity_integral (m:=k) V)) ltac:(by rewrite hv).
apply: (@measure_almost_everywhere_mono R (orthogonal_projection_metric_space R n k)
  (@orthogonal_projection_probability R n k hkn) (@theta_star_is_measure R n k hkn) _ _ _ hh).
move=> p [z [hz hzfin]]; change (projection_multiplicity_integral V p=z) in hz.
by rewrite /= hz.
Qed.
