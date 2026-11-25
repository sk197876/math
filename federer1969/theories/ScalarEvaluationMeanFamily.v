(** Federer (1969), 4.1.5, p. 350:
    the original scalar integral means depend
    uniformly continuously on the target vector.
    This supplies the closedness step in the
    simultaneous differentiation argument, using
    only earlier finite integral and covering laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureUP MeasureBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureSubsetIntegral MeasurableFunctionUP
  SummableRealFunctionUP MeasureDerivationContext CoveringFamilyUP CoveringRelationUP
  MetricDiameter BorelRegularMeasureUP MeasureMeanFunction FiniteMeanPartValues
  LocalAbsoluteIntegrability RealSubsetFiniteDifference FiniteSubsetRealConstantBounds CoveringLipschitzFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarEvaluationMeanFamily.
Variable R:realType.
Variable X Y:metricType R.
Variable mu:set X->\bar R.
Variable V:X->set X->Prop.
Hypothesis hContext:is_measure_derivation_context mu V.
Variable f:Y->X->R.
Hypothesis hMeasurable:forall y,is_measure_measurable_function mu (real_total_integrand (f y)).
Hypothesis hLocal:forall y,is_locally_absolutely_integrable mu (real_total_integrand (f y)).
Hypothesis hPointwise:forall y z x,`|f y x-f z x|<=mdist y z.
Let hClass:=derivation_context_measure hContext.
Let hm:=derivation_measure_law hClass.
Local Notation u := (fun y=>measure_mean_function mu (real_total_integrand (f y))).

(** Source for [scalar_evaluation_mean_family]: the
    uniform target-vector continuity behind the
    simultaneous quotient formula of Federer
    4.1.5, p. 350. Common domains
    are exactly the positive finite-mass cells. *)
Theorem scalar_evaluation_mean_family:is_covering_lipschitz_family V u 1.
Proof.
have hCell x S:V x S ->(extended_metric_diameter S<1%:E)%E ->
    measure_measurable mu S /\mu S \is a fin_num /\
    forall y,exists a:R,is_measure_subset_integral mu S (real_total_integrand (f y)) a%:E.
  move=>hS hDiameter.
  have hBounded:metric_set_bounded S:=lt_trans hDiameter (ltry _).
  have hBorel:=@vitali_relation_borel R X mu V (derivation_context_vitali hContext) S
    (ex_intro _ x (conj Logic.I hS)).
  have hSMeasurable:=@borel_regular_borel_measurable R X mu hm (derivation_measure_borel_regular hClass) S hBorel.
  split=>//; split.
  - by rewrite (ge0_fin_numE (measure_nonnegative hm S)); exact:(@derivation_measure_bounded_finite R X mu hClass S hBounded).
  - move=>y.
    have[a [b [_ [_ hIntegral]]]]:=@locally_absolutely_integrable_part_values R X mu
      (real_total_integrand (f y)) hm (hMeasurable y) (hLocal y) S hBounded hSMeasurable.
    by exists (a-b).
have hPositive S y:partial_function_domain (u y) S ->(0<mu S)%E.
  move=>hDomain; rewrite lt_def (measure_nonnegative hm S) andbT.
  apply/negP=>/eqP hZero; exact:(@measure_mean_zero_denominator R X mu _ S hZero hDomain).
have hValues x S y z:V x S ->(extended_metric_diameter S<1%:E)%E ->(0<mu S)%E ->
    exists a b:R,partial_function_graph (u y) S a%:E /\
      partial_function_graph (u z) S b%:E /\`|a-b|<=mdist y z.
  move=>hS hDiameter hPositiveMass.
  have[hSMeasurable [hFinite hIntegral]]:=hCell x S hS hDiameter.
  have[a hA]:=hIntegral y; have[b hB]:=hIntegral z.
  pose mass:=fine (mu S).
  have hMass:mu S=mass%:E by rewrite /mass fineK.
  have hMassPositive:0<mass by move:hPositiveMass; rewrite hMass lte_fin.
  have hDifference:=@real_subset_finite_difference_integral R X mu hm S (f y) (f z) a b hA hB.
  have hBounds x':S x' -> -mdist y z<=f y x'-f z x'<=mdist y z.
    move=>_; by rewrite -ler_norml; exact:hPointwise.
  have hDifferenceEmbedded:is_measure_subset_integral mu S
      (partial_function_total (fun x'=>((f y x'-f z x')%:E:extended_real_line R))) (a-b)%:E.
    apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hDifference)=>x' q.
    by rewrite !partial_function_zero_extension_graph real_total_integrand_graph.
  have hIntegralBounds:=@finite_subset_real_constant_bounds R X mu hm S
    (fun x'=>f y x'-f z x') mass (a-b) (-mdist y z) (mdist y z)
    hSMeasurable hMass hBounds hDifferenceEmbedded.
  have hAbs:`|a-b|<=mdist y z*mass.
    rewrite ler_norml; apply/andP; move/andP:hIntegralBounds=>[hLo hHi]; split=>//; by rewrite mulNr in hLo.
  exists (a/mass),(b/mass); split.
  - exact:(finite_measure_mean_value hA hMass hMassPositive).
  - split; first exact:(finite_measure_mean_value hB hMass hMassPositive).
    by rewrite -mulrBl normrM normfV (ger0_norm (ltW hMassPositive))
      ler_pdivrMr //.
constructor.
- move=>x S hS hDiameter y z hDomain.
  have[a [b [_ [hB _]]]]:=hValues x S y z hS hDiameter (hPositive S y hDomain).
  by exists b%:E.
- move=>x S hS hDiameter y a hA.
  have[b [c [hB _]]]:=hValues x S y y hS hDiameter (hPositive S y (ex_intro _ a hA)).
  have hEq:=partial_function_single_valued hA hB; by rewrite hEq fin_numE.
- move=>x S hS hDiameter y z a b hA hB.
  have[c [d [hC [hD hBound]]]]:=hValues x S y z hS hDiameter (hPositive S y (ex_intro _ a%:E hA)).
  have hAC:=partial_function_single_valued hA hC.
  have hBD:=partial_function_single_valued hB hD.
  have hEqualA:a=c by injection hAC.
  have hEqualB:b=d by injection hBD.
  by rewrite hEqualA hEqualB.
Qed.
End ScalarEvaluationMeanFamily.
