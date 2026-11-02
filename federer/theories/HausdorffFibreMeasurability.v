(** Federer (1969), 2.10.26, pp. 189–190: the two asserted measurability
    conclusions for a boundedly compact source and a finite measurable set
    A. Increasing compact inner approximation and the proved null-fibre
    reduction implement the printed proof. The target remains an arbitrary
    metric space. The historical questions preceding the theorem are not
    additional project axioms or claimed solutions. Neither is attributed
    the fibre theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzConstant NormMetricScaleContinuity LipschitzFunctionCompact
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs CompactFibreMeasurability
  CompactUnionFibreMeasurability NullFibresProperSource ProperMetricCompactApproximation
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableAlmostModification MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_fibre_measurability_proper_source]: direct
    two-part theorem at the end of 2.10.26,
    p. 189, proved on p. 190. Use any
    proved nonnegative Lipschitz bound. Keep source
    properness, finite source measure and measurability
    of A; add no properness or completeness of Y. *)
Theorem hausdorff_fibre_measurability_proper_source (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (A : set X) k m :
  metric_boundedly_compact X -> is_metric_lipschitz_bound setT f L ->
  measure_measurable (@hausdorff_measure R X (k+m)) A -> @hausdorff_measure R X (k+m) A< +oo ->
  is_measure_measurable_function (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k)) /\
  measure_almost_everywhere (@hausdorff_measure R Y m)
    [set y | measure_measurable (@hausdorff_measure R X k) (A `&` f @^-1` [set y])].
Proof.
move=> hX hf hA hfinite.
have hcont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x z.
  exact: hf.2 x z Logic.I Logic.I.
have hm := @hausdorff_measure_is_measure R Y m.
case: (pselect (A!=set0))=> [[a ha]|hempty]; last first.
  have hAz : A=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  have hAc : compact A by rewrite hAz; exact: compact0.
  split; first exact: compact_hausdorff_fibre_mass_measurable hcont hAc.
  apply: (@measure_almost_everywhere_mono R Y _ hm setT _ _ (measure_almost_everywhere_true hm))=> y _.
  exact: (@compact_hausdorff_fibres_measurable R X Y f A k hcont hAc y).
have [K [hK [hKA [hinc hrest]]]] := @proper_metric_finite_compact_approximation R X
  (@hausdorff_measure R X (k+m)) (@hausdorff_measure_is_measure R X (k+m))
  (@hausdorff_measure_borel_regular R X (k+m)) A a hX hA hfinite.
pose B := \bigcup_n K n.
pose N := A `\` B.
have hBA : B `<=` A by move=> x [n _ hx]; exact: hKA n x hx.
have hgood := @null_hausdorff_fibres_proper_source R X Y f L N k m hX hf hrest.
have hpoint y (hy : hausdorff_fibre_mass f N k y=0) :
    measure_measurable (@hausdorff_measure R X k) (A `&` f @^-1` [set y]) /\
    hausdorff_fibre_mass f A k y=hausdorff_fibre_mass f B k y.
  pose C := B `&` f @^-1` [set y].
  pose D := A `&` f @^-1` [set y].
  pose E := N `&` f @^-1` [set y].
  have hE : @hausdorff_measure R X k E=0 := hy.
  have he x (hxE : ~ E x) : C x <-> D x.
    split; first by move=> [hx hxy]; split=> //; exact: hBA x hx.
    move=> [hx hxy]; split=> //; apply: contrapT=> hxB; apply: hxE; by split=> //; split.
  have hC : measure_measurable (@hausdorff_measure R X k) C.
    exact: (@countable_compact_union_fibres_measurable R X Y f K k hcont hK y).
  split.
  - exact: (@measurable_set_null_modification R X (@hausdorff_measure R X k)
      (@hausdorff_measure_is_measure R X k) C D E hE he hC).
  - exact: esym (@measure_null_modification_value R X (@hausdorff_measure R X k)
      (@hausdorff_measure_is_measure R X k) C D E hE he).
split.
- have hB : is_measure_measurable_function (@hausdorff_measure R Y m)
      (partial_function_total (hausdorff_fibre_mass f B k)).
    exact: increasing_compact_fibre_mass_measurable hcont hK hinc.
  apply: (@measurable_function_almost_equal R Y (extended_real_line R) _ hm _ _ hB).
  apply: (@measure_almost_everywhere_mono R Y _ hm _ _ _ hgood)=> y hy.
  exists (hausdorff_fibre_mass f B k y); split=> //; exact: (hpoint y hy).2.
- apply: (@measure_almost_everywhere_mono R Y _ hm _ _ _ hgood)=> y hy.
  exact: (hpoint y hy).1.
Qed.

(** Source for [federer_2_10_26]: direct two measurability
    conclusions of 2.10.26, pp. 189–190,
    with exactly the printed geometric hypotheses and
    natural-degree Hausdorff interfaces. The preceding
    historical questions are not asserted as theorems. *)
Theorem federer_2_10_26 (R : realType) (X Y : metricType R)
    (f : X -> Y) (hf : is_metric_lipschitz setT f) (A : set X) k m :
  metric_boundedly_compact X ->
  measure_measurable (@hausdorff_measure R X (k+m)) A -> @hausdorff_measure R X (k+m) A< +oo ->
  is_measure_measurable_function (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k)) /\
  measure_almost_everywhere (@hausdorff_measure R Y m)
    [set y | measure_measurable (@hausdorff_measure R X k) (A `&` f @^-1` [set y])].
Proof.
move=> hX.
exact: hausdorff_fibre_measurability_proper_source hX
  (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hf)).
Qed.
