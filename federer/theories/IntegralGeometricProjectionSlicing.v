(** Federer (1969), 2.10.16, p. 178, last displayed formula: average N(p
    restricted to A,y) with I_1^m on R^k and theta*_{n,k}, then multiply by
    beta_1(k,m)/beta_1(n,m). The actual inner and outer integrals are
    proved. The proof exchanges the two projection averages, using the
    composed counting calculation and the normalized marginal law. The
    working Federer erratum has no entry for p. 178. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  EuclideanProjectionComposition ProjectionCompositionAverages IntegralGeometricProjectionSlice
  OrthogonalProjectionProbability ProjectionBeta IntegralGeometricMeasure ProjectionMultiplicityIntegral
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialProductSections
  PartialExtendedOrderLoci MeasureUpperIntegralScale
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralScaleLaw MeasureNonnegativeIntegral PositiveCharacteristicMeasurability
  ProductMeasure ProductFunctionFubini CountablyMeasurableUP CountablyMeasurableBasic
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  ParameterizedIntegral TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_16_projections]: direct final
    formula of 2.10.16, p. 178, with the printed
    1<=m<k<n and Borel A hypotheses. The first conclusion
    exhibits the actual outer integral and its value; the
    second is the printed normalized iterated-integral equality. *)
Theorem federer_2_10_16_projections (R : realType) (n k m : nat)
    (hkn : (k<=n)%N) (hmk : (m<=k)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> (m<k)%N -> (k<n)%N -> borel_set A ->
  is_measure_integral (@orthogonal_projection_probability R n k hkn)
    (partial_function_total (@projection_slice_multiplicity_integral R n k m hmk A))
    ((@projection_beta R n m (leq_trans hmk hkn) 1 /
      @projection_beta R k m hmk 1)%R%:E*
      @integral_geometric_measure R n m (leq_trans hmk hkn) 1 A) /\
  @integral_geometric_measure R n m (leq_trans hmk hkn) 1 A=
    (@projection_beta R k m hmk 1 /
      @projection_beta R n m (leq_trans hmk hkn) 1)%R%:E*
      measure_lower_integral (@orthogonal_projection_probability R n k hkn)
        (partial_function_total (@projection_slice_multiplicity_integral R n k m hmk A)).
Proof.
move=> hmpos hmklt hknlt hA.
have [C hC] := @euclidean_projection_composition_exists R n k m.
pose Q := orthogonal_projection_metric_space R k m.
pose P := orthogonal_projection_metric_space R n k.
pose alpha := @orthogonal_projection_probability R k m hmk.
pose beta := @orthogonal_projection_probability R n k hkn.
pose ha := @theta_star_is_measure R k m hmk.
pose hb := @theta_star_is_measure R n k hkn.
pose mu := product_measure ha hb.
have hm := product_measure_is_measure ha hb.
pose g (z : Q*P) := projection_multiplicity_integral A (C z).
have hg := @projection_composite_parameters_measurable R n k m hkn hmk C A hC hA.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total g)).
  apply: (@measure_almost_everywhere_mono R (Q*P)%type mu hm setT _ _ (measure_almost_everywhere_true hm))=> z _.
  exists (g z); split=> //; exact: projection_multiplicity_integral_nonnegative hA.
have [hi _] := @nonnegative_measurable_function_integral R (Q*P)%type mu hm (partial_function_total g) hg hp.
pose J := measure_lower_integral mu (partial_function_total g).
have hqa : measure_countably_measurable alpha setT.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole ha.
  by rewrite /alpha theta_star_total ltry.
have hpb : measure_countably_measurable beta setT.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole hb.
  by rewrite /beta theta_star_total ltry.
have hc : is_countably_measure_measurable_function mu (0 : extended_real_line R) (partial_function_total g).
  exact: (@countably_measurable_function_on_countable_source R (Q*P)%type (extended_real_line R)
    mu hm 0 _ (@extended_real_zero_closed R) (@product_whole_countably_measurable R Q P alpha beta ha hb hqa hpb) hg).
have [hq hpout] := @product_function_fubini R Q P alpha beta ha hb (partial_function_total g) J hi hc.
pose a := @projection_beta R n m (leq_trans hmk hkn) 1.
pose b := @projection_beta R k m hmk 1.
pose I := @integral_geometric_measure R n m (leq_trans hmk hkn) 1 A.
have ha0 : (0<a)%R := @projection_beta_positive R n m (leq_trans hmk hkn) 1 (lexx _).
have hb0 : (0<b)%R := @projection_beta_positive R k m hmk 1 (lexx _).
have hane : a!=0%R by rewrite gt_eqF.
have hbne : b!=0%R by rewrite gt_eqF.
have hIq : is_measure_integral alpha (partial_function_total (fun _ : Q => (a%:E*I : extended_real_line R))) J.
  apply: (@measure_integral_graph_equivalent R Q alpha _ _ J _ hq)=> q z.
  rewrite parameterized_integral_specification.
  have hsec := @projection_composite_fixed_left_integral R n k m hkn hmk C A q hC hmpos hA.
  change (is_measure_integral beta (partial_function_total (fun p => g (q,p))) z <-> a%:E*I=z).
  split; first by move=> hz; exact: esym (measure_integral_unique hz hsec).
  by move=> <-.
have hconstpos : 0<=a%:E*I.
  have hi0 : 0<=I := measure_nonnegative (@integral_geometric_measure_is_measure R n m (leq_trans hmk hkn) 1 (lexx _)) A.
  have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha0.
  exact: mule_ge0 haE hi0.
have hconst := @nonnegative_extended_constant_integral R Q alpha ha (a%:E*I) hconstpos.
rewrite /alpha theta_star_total mule1 in hconst.
have heJ : J=a%:E*I := measure_integral_unique hIq hconst.
pose s := @projection_slice_multiplicity_integral R n k m hmk A.
have his : is_measure_integral beta (partial_function_total (fun p => (b%:E*s p : extended_real_line R))) J.
  apply: (@measure_integral_graph_equivalent R P beta _ _ J _ hpout)=> p z.
  rewrite parameterized_integral_specification.
  have hsec := @projection_sliced_parameter_integral R n k m hmk C A p hC hA.
  change (is_measure_integral alpha (partial_function_total (fun q => g (q,p))) z <-> b%:E*s p=z).
  split; first by move=> hz; exact: esym (measure_integral_unique hz hsec).
  by move=> <-.
have hbinvpos : (0<b^-1)%R by rewrite invr_gt0.
have hscaled := @measure_integral_positive_scale R P beta hb (b^-1)%R
  (partial_function_total (fun p => (b%:E*s p : extended_real_line R))) J
  hbinvpos his.
have hcancel z : ((b^-1)%R)%:E*(b%:E*z)=z.
  by rewrite muleA -EFinM mulVf // mul1e.
have hslice : is_measure_integral beta (partial_function_total s) (((b^-1)%R)%:E*J).
  apply: (@measure_integral_graph_equivalent R P beta _ _ _ _ hscaled)=> p z.
  split.
  - move=> [w [hw hwz]]; rewrite -(hw : b%:E*s p=w) hcancel in hwz; exact hwz.
  - move=> hz; exists (b%:E*s p); split=> //; by rewrite hcancel.
have hevalue : ((b^-1)%R)%:E*J=(a/b)%R%:E*I.
  by rewrite heJ muleA -EFinM mulrC.
rewrite hevalue in hslice.
split; first exact hslice.
have he := measure_lower_integral_unique (measure_lower_integral_specification beta _) hslice.2.2.
rewrite he muleA -EFinM.
have hfactor : ((b/a)*(a/b)= 1)%R.
  by rewrite -mulrA [(a^-1*(a*b^-1))%R]mulrA
    (mulVf hane) mul1r (mulfV hbne).
by rewrite hfactor mul1e.
Qed.
