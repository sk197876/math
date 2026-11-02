(** Federer (1969), 3.2.20, p. 257: every compact
    chart has the proved local transformation, their source densities
    sum off the null remainder, and their actual fibre counts sum
    off its null image. No decomposition law is assumed in the
    resulting area theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  PartialZeroExtension MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence
  HausdorffMeasure HausdorffLipschitzImages MappingMultiplicity MappingMultiplicityLaws CountingMeasure
  NonnegativeSum TotalNonnegativeSeriesIntegral TotalScalarCutoff WeightedScalarCutoff DisjointScalarCutoffSeries
  RectifiableCompactChartsUP RectifiableCompactChartLaws MeasureApproximateJacobian
  RectifiableChartJacobianIntegral RectifiableChartAreaTransform EuclideanFiniteMassMultiplicity
  MappingMultiplicityDisjointCover CountableAreaDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_area_chart_decomposition]: supporting
    full discharge of the compact-cover summation in Federer
    3.2.20, p. 257. All local integral transformations,
    measurable densities, finite multiplicity and count identities
    follow from the given proved chart cover and exact intrinsic
    Jacobian graph. No derivative field, source-measurable preimage,
    ambient Radon property or additional rank premise is assumed. *)
Theorem rectifiable_area_chart_decomposition (R : realType) m n k
    (lambda : R) (W : set (R_n R n))
    (K : nat -> set (R_n R m)) (psi : nat -> R_n R m -> R_n R n)
    (F : R_n R n -> R_n R k) (J : R_n R n -> R) :
  (1<lambda)%R -> is_rectifiable_compact_chart_cover lambda W K psi ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  (forall w,(0<=J w)%R) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
      (partial_function_source_restrict W (partial_function_total F))) J ->
  is_countable_area_decomposition
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
    F (fun z=>z) (total_scalar_cutoff W J)
    (fun i=>total_scalar_cutoff (psi i @` K i) J)
    (fun z=>@mapping_multiplicity R _ _ F W z)
    (fun i z=>@mapping_multiplicity R _ _ F (psi i @` K i) z).
Proof.
move=> hLam hCover hW hFin hF hJ0 hJExt.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose beta := @hausdorff_measure R Y m.
pose gamma := @hausdorff_measure R Z m.
have hb := @hausdorff_measure_is_measure R Y m.
have hg := @hausdorff_measure_is_measure R Z m.
pose E i := psi i @` K i.
pose p := total_scalar_cutoff W J.
pose pi i := total_scalar_cutoff (E i) J.
have hSub i : E i `<=` W := (hCover.1 i).2.
have hDisj i j : i!=j -> forall w,E i w -> E j w -> False := hCover.2.1 i j.
have hLoss : beta (W `\` (\bigcup_i E i))=0 := hCover.2.2.
have hEach i : exists a,
    is_measure_integral beta (partial_function_total (fun w=>(pi i w)%:E : extended_real_line R)) a /\
    is_measure_integral gamma (partial_function_total
      (fun z=>(@mapping_multiplicity R Y Z F (E i) z:extended_real_line R))) a.
  have [a [hI hN]] := @rectifiable_compact_chart_jacobian_integral R m n k lambda W (K i) (psi i) F J
    hLam (hCover.1 i).1 (hCover.1 i).2 hW hFin hF hJExt.
  exists a; split; last exact hN.
  exact: (measure_integral_graph_equivalent (@scalar_cutoff_embedding_graph R Y (E i) J) hI).
have [a ha] := choice hEach.
have hPI i : is_measure_integral beta (partial_function_total (fun w=>(pi i w)%:E : extended_real_line R)) (a i).
  exact: (ha i).1.
have hNiI i : is_measure_integral gamma (partial_function_total
    (fun z=>(@mapping_multiplicity R Y Z F (E i) z:extended_real_line R))) (a i).
  exact: (ha i).2.
have [hPiBounds hPSum] := @disjoint_scalar_cutoff_series R Y beta hb W E J hJ0 hSub hDisj hLoss.
have hp0 w : (0<=p w)%R := @nonnegative_scalar_cutoff R Y W J hJ0 w.
have hPi0 i w : 0<=(pi i w)%:E.
  rewrite lee_fin; exact: (andP (hPiBounds i w)).1.
have hSeries := total_nonnegative_series_integral hb hPi0 hPI.
have hPAE : measure_almost_equal beta
    (partial_function_total (fun w=>(nonnegative_sum setT (fun i=>(pi i w)%:E):extended_real_line R)))
    (partial_function_total (fun w=>(p w)%:E:extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y beta hb _ _ _ hPSum)=> w hw.
  exists (p w)%:E; split; first exact hw; reflexivity.
have hPIntegral := measure_integral_almost_equal hb hSeries hPAE.
have [hNMeas hNFinite] := euclidean_finite_mass_multiplicity hF hW hFin.
have hImageLoss : gamma (F @` (W `\` (\bigcup_i E i)))=0.
  have [L [hL hFL]] := hF.
  have hh := @hausdorff_lipschitz_image_bound R Y Z F L m hFL (W `\` (\bigcup_i E i)).
  change (is_true (gamma (F @` (W `\` (\bigcup_i E i)))<=(L^+m)%R%:E*beta (W `\` (\bigcup_i E i)))) in hh.
  rewrite hLoss mule0 in hh; apply/eqP; rewrite eq_le hh (measure_nonnegative hg); reflexivity.
have hNSum := @mapping_multiplicity_almost_disjoint_cover R Y Z gamma hg F W E hSub hDisj hImageLoss.
constructor.
- exact hp0.
- exact hPiBounds.
- exact hPIntegral.1.
- move=> i; exact: (hPI i).1.
- exact hPSum.
- move=> z; exact: (@mapping_multiplicity_nonnegative R Y Z F W z).
- move=> i z; apply/andP; split; first exact: (@mapping_multiplicity_nonnegative R Y Z F (E i) z).
  apply: (@measure_mono R Y (@counting_measure R Y) (counting_measure_is_measure R Y)).
  by move=> w [hw hVal]; split; first exact: hSub i w hw.
- exact hNMeas.
- move=> i; exact: (hNiI i).1.
- exact hNFinite.
- exact hNSum.
- move=> g i b.
  have hLocal := @rectifiable_compact_chart_area_transform R m n k lambda W (K i) (psi i) F J
    hLam (hCover.1 i).1 (hCover.1 i).2 hW hFin hF hJExt g b.
  have hGraph := @weighted_scalar_cutoff_graph R Y (E i) (fun w=>g (F w)) J.
  split=> hI.
  + have hSubset := measure_integral_graph_equivalent (fun w t=>iff_sym (hGraph w t)) hI.
    exact: hLocal.1 hSubset.
  + exact: (measure_integral_graph_equivalent hGraph (hLocal.2 hI)).
Qed.
