(** Federer (1969), 2.4.19, p. 91: integration of F on a finite image. This
    supporting finite sum is derived from characteristic integrals and null
    invariance, with F nonnegative only on the actual image. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureStepFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureCharacteristicIntegral MeasureStepIntegralIdentification MeasureFiniteRealScaleIntegral
  MeasureFiniteRealSumIntegral FiniteFibreMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_delta_weighted_values]: supporting recovery of
    F(f(x)) from the characteristic fibres in the finite-image case of
    Federer 2.4.19, p. 91 The labels and the scalar values may differ. *)
Lemma finite_delta_weighted_values (R : realType) (I : eqType)
    (s : seq I) (v : I) (c F : I -> R) :
  uniq s -> v \in s -> c v= 1%R -> (forall y, y != v -> c y=0%R) ->
  (\sum_(y <- s) F y * c y)%R=F v.
Proof.
move=> hs hv hc hz; rewrite (bigD1_seq v) // hc mulr1.
have hzero : (\sum_(y <- s | y != v) F y * c y)%R=0%R.
  apply: big1=> y hy; by rewrite (hz y hy) mulr0.
rewrite hzero; change ((F v+0)%R=F v); by rewrite addr0.
Qed.

(** Source for [finite_scalar_composite_integral_formula]: supporting
    finite-image scalar integral in Federer 2.4.19, p. 91 Continuity of F is
    unnecessary on a finite image. Conull partial domains are retained. *)
Theorem finite_scalar_composite_integral_formula (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (F : V -> R) :
  mu setT < +oo -> is_measure_measurable_function mu f -> finite_set (partial_function_range f) ->
  (forall y, partial_function_range f y -> (0 <= F y)%R) ->
  is_measure_integral mu (partial_function_postcompose f (fun y => ((F y)%:E : extended_real_line R)))
    (\sum_(y <- fset_set (partial_function_range f)) F y * fine (mu (partial_function_preimage f [set y])))%R%:E.
Proof.
move=> hmass hf hfin hF; pose S := fset_set (partial_function_range f).
pose A y := partial_function_preimage f [set y].
pose s y := @CharacteristicFunction.value R X (A y).
have hs y := @CharacteristicFunction.laws R X (A y).
have hA y := @finite_source_function_fibre R X V N hN mu hm f y hmass hf.
pose b y := fine (mu (A y)).
have hb y : mu (A y)=(b y)%:E by rewrite /b fineK //; exact: (hA y).2.
have hb0 y : (0 <= b y)%R by have h := measure_nonnegative hm (A y); rewrite hb lee_fin in h.
have hi y : y \in S -> is_measure_integral mu
    (partial_real_function_embed (partial_function_total (fun x => ((F y * s y x)%R : real_line_metric R))))
    (F y * b y)%R%:E.
  move=> _; have hchar := @measure_characteristic_integral R X mu hm (A y) (s y) (hs y) (hA y).1.
  rewrite hb in hchar.
  exact: (@measure_finite_real_total_scale_integral R X mu hm (s y) (b y) (F y) hchar).
have hnon y : y \in S -> 0 <= (F y * b y)%R%:E.
  move=> hy; rewrite lee_fin; apply: mulr_ge0; last exact: hb0.
  apply: hF; move: hy; rewrite /S in_fset_set //; exact: set_mem.
have hsum := @measure_finite_real_sum_integral R X V mu hm (S : seq V)
  (fun y x => ((F y * s y x)%R : real_line_metric R)) (fun y => (F y * b y)%R%:E) hnon hi.
rewrite sumEFin in hsum.
apply: (@measure_integral_almost_equal R X mu hm _ _ _ hsum).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
move=> x [v hv]; exists (F v)%:E; split; last by exists v; split.
have hvS : v \in S.
  rewrite /S in_fset_set //; apply/mem_set; by exists x.
have hcv : s v x= 1%R.
  apply: (characteristic_on_set (hs v)); exists v; by split.
have hc0 y : y != v -> s y x=0%R.
  move=> hy; apply: (characteristic_off_set (hs y))=> [[z [hz he]]].
  have hvz := partial_function_single_valued hv hz.
  apply: (negP hy); apply/eqP; by rewrite -hvz in he; symmetry.
exists (F v); split=> //.
exact: (@finite_delta_weighted_values R V (S : seq V) v (fun y => s y x) F (fset_uniq S) hvS hcv hc0).
Qed.
