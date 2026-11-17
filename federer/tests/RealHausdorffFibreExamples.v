(** Project endpoint regressions for Federer 2.10.25, pp. 188-189.
    Constant maps test infinite fibres over a null target point and
    the separate zero-target-degree case with 0^0=1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealHausdorffMeasure
  RealHausdorffNormalisation RealHausdorffFibreTheorem RealHausdorffFibreCost
  RealHausdorffFibreCutoffs RealHausdorffNullImageFibres RealPower
  LipschitzUP LipschitzBasic CountingMeasure CountingPair CountingInjectionBound
  AffineCylinderNullSectionCounterexample CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureExtendedCharacteristicIntegral MeasureIntegralBounds MeasureIntegralUniqueness
  PartialFunctionBasic MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_half_target_infinite_constant_fibre]: project
    regression for the zero-Lipschitz-bound endpoint in Federer 2.10.25,
    pp. 188-189. Collapsing the real unit interval gives an infinite
    degree-zero fibre at zero, yet its upper integral against actual
    half-degree Hausdorff measure is zero. Reuse the existing infinite
    count of the unit interval and the proved null-image method. *)
Theorem real_half_target_infinite_constant_fibre (R : realType)
    (hm : (0<=(1/2 : R))%R) :
    @real_hausdorff_fibre_mass R (real_line_metric R) (real_line_metric R)
      (fun _ => 0%R) `[0%R,1%R] 0%R (lexx 0%R) 0%R=+oo /\
    measure_upper_integral (@real_hausdorff_measure R (real_line_metric R) (1/2 : R) hm)
      (partial_function_total (@real_hausdorff_fibre_mass R (real_line_metric R) (real_line_metric R)
        (fun _ => 0%R) `[0%R,1%R] 0%R (lexx 0%R)))=0.
Proof.
split.
- have hs : (`[0%R,1%R] : set (real_line_metric R)) `&`
      (fun _ : real_line_metric R => (0%R : real_line_metric R)) @^-1` [set 0%R]=`[0%R,1%R].
    apply/seteqP; split=> [x [hx _]|x hx] //; by split.
  rewrite /real_hausdorff_fibre_mass hs real_hausdorff_zero_counting.
  exact: (null_scalar_infinite_fibre_counterexample R).2.1.
- apply: (@real_zero_lipschitz_positive_degree_fibre_integral_zero R
    (real_line_metric R) (real_line_metric R) (fun _ => 0%R)
    0%R (1/2 : R) (lexx 0%R) hm `[0%R,1%R]).
  + split; first exact: lexx.
    by move=> x z _ _; rewrite mdistxx mul0r.
  + by rewrite divr_gt0 // ltr0n.
Qed.

(** Source for [real_zero_target_constant_pair]: project regression
    for the zero-target-degree, zero-Lipschitz-bound endpoint in Federer
    2.10.25, pp. 188-189. Collapsing two distinct real points gives
    fibre integral two and coefficient one, rather than coefficient zero.
    Both sides of the original inequality are exactly two. *)
Theorem real_zero_target_constant_pair (R : realType) :
    let X := real_line_metric R in
    let A : set X := [set 0%R] `|` [set 1%R] in
    measure_upper_integral (@real_hausdorff_measure R X 0%R (lexx 0%R))
      (partial_function_total (@real_hausdorff_fibre_mass R X X
        (fun _ => 0%R) A 0%R (lexx 0%R)))=(2 : R)%:E /\
    (real_hausdorff_fibre_bound_constant (lexx (0%R : R)) (lexx (0%R : R)) 0%R)%:E*
      @real_hausdorff_measure R X (0+0)%R (addr_ge0 (lexx 0%R) (lexx 0%R)) A=(2 : R)%:E.
Proof.
move=> X A.
pose h0 := lexx (0%R : R).
pose mu := @real_hausdorff_measure R X 0%R h0.
pose s := @CharacteristicFunction.value R X [set 0%R].
have hs := @CharacteristicFunction.laws R X [set 0%R].
have hm : is_measure mu := @real_hausdorff_measure_is_measure R X 0%R h0.
have hA : @counting_measure R X A=(2 : R)%:E.
  apply: counting_measure_distinct_pair; by rewrite eq_sym oner_eq0.
have hmass : mu [set 0%R] = 1.
  rewrite /mu real_hausdorff_zero_counting; exact: counting_measure_singleton_value.
have hmeas : measure_measurable mu [set 0%R].
  have he : mu=@counting_measure R X by apply: funext => B; exact: real_hausdorff_zero_counting.
  rewrite he; exact: counting_measure_measurable.
have hfun : @real_hausdorff_fibre_mass R X X (fun _ => 0%R) A 0%R h0=
    (fun y => (2 : R)%:E*(s y)%:E).
  apply: funext => y; case: (pselect (y=0%R)) => hy.
  - subst y.
    have he : A `&` (fun _ : X => (0%R : X)) @^-1` [set 0%R]=A.
      apply/seteqP; split=> [x [hx _]|x hx] //; by split.
    rewrite /real_hausdorff_fibre_mass he real_hausdorff_zero_counting hA /s.
    by rewrite (characteristic_on_set hs (erefl (0%R : X))) mule1.
  - have he : A `&` (fun _ : X => (0%R : X)) @^-1` [set y]=set0.
      apply/seteqP; split=> [x [_ hxy]|x []]; exfalso; apply: hy.
      exact: esym hxy.
    have hn : ~ [set (0%R : X)] y := hy.
    by rewrite /real_hausdorff_fibre_mass he
      (measure_empty (@real_hausdorff_measure_is_measure R X 0%R h0))
      /s (characteristic_off_set hs hn) mule0.
split.
- rewrite hfun.
  have htwo : 0<=(2 : R)%:E by rewrite lee_fin ler0n.
  have hi := @measure_nonnegative_extended_characteristic_integral R X mu hm
    [set 0%R] s (2 : R)%:E hs hmeas htwo.
  rewrite hmass mule1 in hi.
  exact: (@measure_upper_integral_unique R X mu _ _ (2 : R)%:E
    (measure_upper_integral_specification mu _) hi.2.1).
- have hnormzero (p : R) (hp : (0<=p)%R) : p=0%R ->
      real_hausdorff_normalisation hp = 1%R.
    move=> he; subst p; exact: real_hausdorff_normalisation_zero.
  have hmasszero (p : R) (hp : (0<=p)%R) : p=0%R ->
      @real_hausdorff_measure R X p hp A=(2 : R)%:E.
    move=> he; subst p; by rewrite real_hausdorff_zero_counting hA.
  have hn := hnormzero (0+0)%R (addr_ge0 h0 h0) (addr0 (0%R : R)).
  have hmasssum := hmasszero (0+0)%R (addr_ge0 h0 h0) (addr0 (0%R : R)).
  by rewrite /real_hausdorff_fibre_bound_constant
    !real_hausdorff_normalisation_zero hn real_power_zero_exponent
    divr1 !mulr1 mul1e hmasssum.
Qed.
