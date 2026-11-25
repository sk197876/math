(** Federer (1969), 3.2.20, p. 257: sum the
    compact-chart integral transformations by 2.4.8, p. 84.
    This supporting transport theorem isolates the nonnegative
    countable sum and preserves possible infinite integral values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasureNonnegativeIntegral NonnegativeSum NonnegativeSumExtendedScale TotalNonnegativeSeriesIntegral
  MeasurableFiniteWeightSubproduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_weighted_integral_transport_forward]: the
    final summation step in Federer 3.2.20, p. 257,
    expanded using 2.4.8, p. 84. Source densities are finite
    and measurable, with each summand dominated by the total density.
    Target densities may be infinite. Sum identities need hold only
    almost everywhere; no measurability of the unweighted g is assumed.
    The chart hypotheses are proved separately in the application. *)
Theorem countable_weighted_integral_transport_forward (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (pi : nat -> X -> R)
    (q : Y -> \bar R) (qi : nat -> Y -> \bar R) :
  (forall x,(0<=p x)%R) ->
  (forall i x,(0<=pi i x<=p x)%R) ->
  (forall i y,0<=qi i y) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  (forall i,is_measure_measurable_function mu
    (partial_function_total (fun x=>(pi i x)%:E : extended_real_line R))) ->
  measure_almost_everywhere mu [set x|nonnegative_sum setT (fun i=>(pi i x)%:E)=(p x)%:E] ->
  measure_almost_everywhere nu [set y|nonnegative_sum setT (fun i=>qi i y)=q y] ->
  (forall (g : Z -> \bar R), (forall z,0<=g z) -> forall i a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (pi i x)%:E : extended_real_line R)) a ->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* qi i y : extended_real_line R)) a) ->
  forall (g : Z -> \bar R), (forall z,0<=g z) -> forall a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (p x)%:E : extended_real_line R)) a ->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* q y : extended_real_line R)) a.
Proof.
move=> hp hpi hqi hpMeas hpiMeas hPSum hQSum hLocal g hg a hI.
pose P i (x : X) : extended_real_line R := g (u x)* (pi i x)%:E.
pose Q i (y : Y) : extended_real_line R := g (v y)* qi i y.
have hP0 i x : 0<=P i x.
  apply: mule_ge0 (hg (u x)) _; rewrite lee_fin; exact: (andP (hpi i x)).1.
have hQ0 i y : 0<=Q i y := mule_ge0 (hg (v y)) (hqi i y).
have hPMeas i : is_measure_measurable_function mu (partial_function_total (P i)).
  exact: (@measurable_finite_weight_subproduct R X mu hm (fun x=>g (u x)) p (pi i)
    hp (hpi i) hpMeas (hpiMeas i) hI.1).
pose b i := measure_lower_integral mu (partial_function_total (P i)).
have hPI i : is_measure_integral mu (partial_function_total (P i)) (b i).
  have hAE : measure_almost_everywhere mu
      (partial_extended_nonnegative_locus (partial_function_total (P i))).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
      (measure_almost_everywhere_true hm))=> x _; exists (P i x); split; first reflexivity.
    exact: hP0.
  exact: (nonnegative_measurable_function_integral hm (hPMeas i) hAE).1.
have hQI i : is_measure_integral nu (partial_function_total (Q i)) (b i).
  exact: (hLocal g hg i (b i) (hPI i)).
have hPSeries := total_nonnegative_series_integral hm hP0 hPI.
have hQSeries := total_nonnegative_series_integral hn hQ0 hQI.
have hPAE : measure_almost_equal mu
    (partial_function_total (fun x=>(nonnegative_sum setT (fun i=>P i x) : extended_real_line R)))
    (partial_function_total (fun x=>g (u x)* (p x)%:E : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hPSum)=> x hx.
  exists (g (u x)* (p x)%:E); split; last reflexivity.
  change (nonnegative_sum setT (fun i=>g (u x)* (pi i x)%:E)=g (u x)* (p x)%:E).
  have hpi0 i (_ : setT i) : 0<=(pi i x)%:E.
    rewrite lee_fin; exact: (andP (hpi i x)).1.
  by rewrite (nonnegative_sum_extended_scale (hg (u x)) hpi0) hx.
have hQAE : measure_almost_equal nu
    (partial_function_total (fun y=>(nonnegative_sum setT (fun i=>Q i y) : extended_real_line R)))
    (partial_function_total (fun y=>g (v y)* q y : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hQSum)=> y hy.
  exists (g (v y)* q y); split; last reflexivity.
  change (nonnegative_sum setT (fun i=>g (v y)* qi i y)=g (v y)* q y).
  by rewrite (nonnegative_sum_extended_scale (hg (v y)) (fun i _=>hqi i y)) hy.
have hIS := measure_integral_almost_equal hm hPSeries hPAE.
have hValue := measure_integral_unique hIS hI.
have hIT := measure_integral_almost_equal hn hQSeries hQAE.
by rewrite hValue in hIT.
Qed.
