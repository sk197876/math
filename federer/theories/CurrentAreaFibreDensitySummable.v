(** Federer (1969), 4.1.25, p. 383: the
    actual target fibre density is Hausdorff summable.
    Its measurable mass is bounded by the original
    scalar mass sum, whose finite integral is supplied
    by 3.2.3. Apply the existing L1 membership and
    null-modification laws of 2.4.12 and 2.3.2;
    no Radon hypothesis on ambient H^m is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading CurrentCoefficientNorms CurrentVectorCompleteness
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralGraphEquivalence MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureLpMembershipUP MeasureLpAlmostEquality SummableRealFunctionUP
  ExtendedRealOrderTopology PartialExtendedOrderLoci
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionExtensionSealed FibreNonnegativeSum TotalVectorNormIntegrability
  CurrentAreaNormalisedImageSealed CurrentAreaFibreDensitySealed
  CurrentAreaFibreDensityMeasurable CurrentAreaFibreDensityMass
  CurrentAreaFibreMassIntegral
  MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section SummableFibreDensity.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable xi : @compact_summable_multivector_space R h2 m m Full hFull.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m Full hFull xi).
Variable f : X -> R_n R n.
Hypothesis hLip : @is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m)) Y setT f.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation hM := (@current_vector_mass_real_norm R h2 n m).
Local Notation r := (fun x => @current_vector_mass R h2 m m (raw x)).
Local Notation size := (@compact_summable_multivector_size R h2 m m Full hFull xi).

(** Source for [current_area_fibre_representative_norm_integral]:
    the finite norm integral of the original fibre
    density in Federer 4.1.25, p. 383.
    A positive Lipschitz bound gives an explicit finite
    bound; the final summability theorem needs only
    the original existence of such a bound. *)
Theorem current_area_fibre_representative_norm_integral
    (w : R_n R n -> V) (L : R) :
  is_partial_function_total_extension eta w ->
  (0 < L)%R -> @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m)) Y setT f L ->
  exists a : R,
    is_measure_integral H (real_total_integrand (fun y => M (w y))) a%:E /\
    (0 <= a <= L^+m*size)%R.
Proof.
move=> hW hL hBound.
have hH := @hausdorff_measure_is_measure R Y m.
have hRaw : is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x => ((r x)%:E : extended_real_line R))) size%:E.
  apply: (measure_integral_graph_equivalent _
    (@compact_summable_multivector_ambient_integral R h2 m m Full hFull xi)) => x z.
  exact: real_total_integrand_graph.
have hMass := @current_area_fibre_density_mass_bound R h2 m n f raw w hLip
  (ex_intro _ size hRaw) hW.
have hSourcePositive x : (0 <= r x)%R.
  exact: real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m m).1 _.
have [b [hMassIntegral hBudget]] := @current_area_fibre_mass_integral R m n f r
  L size hL hBound hSourcePositive hRaw.
have hField := @current_area_fibre_representative_measurable R h2 m n xi f hLip w hW.
have hMeas := @total_vector_norm_integrand_measurable R Y V M hM H hH w hField.
have hPositive : measure_almost_everywhere H
    (partial_extended_nonnegative_locus (real_total_integrand (fun y => M (w y)))).
  apply: (measure_almost_everywhere_mono hH _ (measure_almost_everywhere_true hH)) => y _.
  exists (M (w y))%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: real_seminorm_nonnegative hM.1 _.
have [hNorm hNonnegative] := nonnegative_measurable_function_integral hH hMeas hPositive.
have hOrder : measure_almost_everywhere H
    (partial_extended_le_locus (real_total_integrand (fun y => M (w y)))
      (partial_function_total (fun y =>
        (fibre_nonnegative_sum f (fun x => (r x)%:E) y : extended_real_line R)))).
  apply: (measure_almost_everywhere_mono hH _ hMass) => y hy.
  exists (M (w y))%:E,(fibre_nonnegative_sum f (fun x => (r x)%:E) y).
  split; first by apply/real_total_integrand_graph.
  by split.
have hComparison := measure_integral_monotone hH hNorm hMassIntegral hOrder.
pose c := measure_lower_integral H (real_total_integrand (fun y => M (w y))).
have hFinite : c \is a fin_num.
  rewrite (ge0_fin_numE hNonnegative).
  exact: le_lt_trans hComparison (ltry b).
exists (fine c); split.
- rewrite fineK //; exact: hNorm.
- apply/andP; split.
  + rewrite -lee_fin (fineK hFinite); exact: hNonnegative.
  + have hAB : (fine c <= b)%R.
      rewrite -lee_fin (fineK hFinite); exact: hComparison.
    exact: le_trans hAB (andP hBudget).2.
Qed.

(** Source for [current_area_fibre_representative_lone]:
    actual L1 membership of every total representative
    of the fibre density in Federer 4.1.25,
    p. 383, including countable measurability and
    the finite-dimensional coefficient-range condition. *)
Theorem current_area_fibre_representative_lone (w : R_n R n -> V) :
  is_partial_function_total_extension eta w ->
  is_measure_lp_function H 1%R
    (partial_function_total (fun y => (w y : real_norm_metric_space hM))).
Proof.
move=> hW; have [L [hL hBound]] := hLip.
have [a [hIntegral _]] := current_area_fibre_representative_norm_integral hW hL hBound.
exact: (@total_vector_lone_from_norm_integral R Y V M hM H
  (@hausdorff_measure_is_measure R Y m) w a
  (@current_multivector_mass_separable R h2 n m)
  (@current_area_fibre_representative_measurable R h2 m n xi f hLip w hW) hIntegral).
Qed.

(** Source for [current_area_fibre_density_lone]:
    the literal original partial fibre density is
    Hausdorff summable, as stated in Federer 4.1.25,
    p. 383. Its conull domain is retained through
    the original L1 null-modification theorem. *)
Theorem current_area_fibre_density_lone :
  is_measure_lp_function H 1%R
    (eta : partial_function Y (real_norm_metric_space hM)).
Proof.
pose w := @PartialFunctionExtension.value Y V eta 0%R.
have hW : is_partial_function_total_extension eta w :=
  @PartialFunctionExtension.laws Y V eta 0%R.
have hLone := current_area_fibre_representative_lone hW.
have hEta := @current_area_fibre_density_measurable R h2 m n xi f hLip.
have hDomain := measurable_function_domain hEta.
apply: (measure_lp_function_almost_equal (@hausdorff_measure_is_measure R Y m) hLone).
apply: (measure_almost_everywhere_mono (@hausdorff_measure_is_measure R Y m) _ hDomain)
  => y [v hValue].
exists v; split; first exact: hW y v hValue.
exact: hValue.
Qed.
End SummableFibreDensity.
