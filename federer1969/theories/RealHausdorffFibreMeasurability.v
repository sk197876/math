(** Federer (1969), 2.10.26, pp. 189–190: the two asserted measurability
    conclusions for a boundedly compact source and a finite measurable set
    A. Increasing compact inner approximation and the proved null-fibre
    reduction implement the printed proof. The target remains an arbitrary
    metric space. The historical questions preceding the theorem are not
    additional project assumptions or claimed solutions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffFibreCutoffs ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzConstant NormMetricScaleContinuity LipschitzFunctionCompact
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs CompactRealFibreMeasurability
  CompactRealUnionFibreMeasurability RealNullFibresProperSource ProperMetricCompactApproximation
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableAlmostModification MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_fibre_measurability_proper_source]: direct
    two-part theorem at the end of 2.10.26,
    p. 189, proved on p. 190. Use any
    proved nonnegative Lipschitz bound. Keep source
    properness, finite source measure and measurability
    of A; add no properness or completeness of Y. *)
Theorem real_hausdorff_fibre_measurability_proper_source (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  metric_boundedly_compact X -> is_metric_lipschitz_bound setT f L ->
  measure_measurable (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm)) A -> @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  is_measure_measurable_function (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f A hk)) /\
  measure_almost_everywhere (@real_hausdorff_measure R Y m hm)
    [set y | measure_measurable (@real_hausdorff_measure R X k hk) (A `&` f @^-1` [set y])].
Proof.
move=> hX hf hA hfinite.
have hcont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x z.
  exact: hf.2 x z Logic.I Logic.I.
have hMeasure := @real_hausdorff_measure_is_measure R Y m hm.
case: (pselect (A!=set0))=> [[a ha]|hempty]; last first.
  have hAz : A=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  have hAc : compact A by rewrite hAz; exact: compact0.
  split; first exact: compact_real_hausdorff_fibre_mass_measurable hcont hAc.
  apply: (@measure_almost_everywhere_mono R Y _ hMeasure setT _ _ (measure_almost_everywhere_true hMeasure))=> y _.
  exact: (@compact_real_hausdorff_fibres_measurable R X Y f A k hk hcont hAc y).
have [K [hK [hKA [hinc hrest]]]] := @proper_metric_finite_compact_approximation R X
  (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm)) (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm))
  (@real_hausdorff_measure_borel_regular R X (k+m)%R (addr_ge0 hk hm)) A a hX hA hfinite.
pose B := \bigcup_n K n.
pose N := A `\` B.
have hBA : B `<=` A by move=> x [n _ hx]; exact: hKA n x hx.
have hgood := @null_real_hausdorff_fibres_proper_source R X Y f L N k m hk hm hX hf hrest.
have hpoint y (hy : real_hausdorff_fibre_mass f N hk y=0) :
    measure_measurable (@real_hausdorff_measure R X k hk) (A `&` f @^-1` [set y]) /\
    real_hausdorff_fibre_mass f A hk y=real_hausdorff_fibre_mass f B hk y.
  pose C := B `&` f @^-1` [set y].
  pose D := A `&` f @^-1` [set y].
  pose E := N `&` f @^-1` [set y].
  have hE : @real_hausdorff_measure R X k hk E=0 := hy.
  have he x (hxE : ~ E x) : C x <-> D x.
    split; first by move=> [hx hxy]; split=> //; exact: hBA x hx.
    move=> [hx hxy]; split=> //; apply: contrapT=> hxB; apply: hxE; by split=> //; split.
  have hC : measure_measurable (@real_hausdorff_measure R X k hk) C.
    exact: (@countable_compact_real_union_fibres_measurable R X Y f K k hk hcont hK y).
  split.
  - exact: (@measurable_set_null_modification R X (@real_hausdorff_measure R X k hk)
      (@real_hausdorff_measure_is_measure R X k hk) C D E hE he hC).
  - exact: esym (@measure_null_modification_value R X (@real_hausdorff_measure R X k hk)
      (@real_hausdorff_measure_is_measure R X k hk) C D E hE he).
split.
- have hB : is_measure_measurable_function (@real_hausdorff_measure R Y m hm)
      (partial_function_total (real_hausdorff_fibre_mass f B hk)).
    exact: increasing_compact_real_fibre_mass_measurable hcont hK hinc.
  apply: (@measurable_function_almost_equal R Y (extended_real_line R) _ hMeasure _ _ hB).
  apply: (@measure_almost_everywhere_mono R Y _ hMeasure _ _ _ hgood)=> y hy.
  exists (real_hausdorff_fibre_mass f B hk y); split=> //; exact: (hpoint y hy).2.
- apply: (@measure_almost_everywhere_mono R Y _ hMeasure _ _ _ hgood)=> y hy.
  exact: (hpoint y hy).1.
Qed.

(** Source for [federer_2_10_26_real]: direct two measurability
    conclusions of 2.10.26, pp. 189–190,
    with exactly the printed geometric hypotheses and
    actual Gamma-normalized real-degree Hausdorff measures. The preceding
    historical questions are not asserted as theorems. *)
Theorem federer_2_10_26_real (R : realType) (X Y : metricType R)
    (f : X -> Y) (hf : is_metric_lipschitz setT f) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  metric_boundedly_compact X ->
  measure_measurable (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm)) A -> @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  is_measure_measurable_function (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f A hk)) /\
  measure_almost_everywhere (@real_hausdorff_measure R Y m hm)
    [set y | measure_measurable (@real_hausdorff_measure R X k hk) (A `&` f @^-1` [set y])].
Proof.
move=> hX.
exact: real_hausdorff_fibre_measurability_proper_source hX
  (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hf)).
Qed.
