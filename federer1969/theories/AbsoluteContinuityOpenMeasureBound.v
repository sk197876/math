(** Federer (1969), 2.9.20, p. 166, second consequent implication of (3):
    small open subsets of (a,b) have small sum of induced-measure masses. We
    use the project's increasing finite dyadic cell unions, rather than
    constructing all connected components of the open set; the finite
    disjoint-union and continuity-below argument is the same. Source
    editions: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength StieltjesImageMeasures
  StieltjesInducedPairLaws StieltjesDerivationClass MeasureDerivationContext
  RealAbsoluteContinuityUP RealAbsoluteContinuityBasic SegmentRelativeContinuity
  AbsoluteContinuityFamilyVariation IntervalFamilyNearVariation OrderedIntervalFamilyUP
  DyadicIntervalFamilies DyadicFamilyMasses LebesgueLineCharacterisation HalfOpenAtomRemoval
  MeasureUP MeasureBasic MeasureBinaryAddition MeasureContinuityBelow ExtendedRealLimitBounds
  LebesgueScalarMeasure BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [absolute_continuity_open_induced_mass_bound]: direct second
    consequent implication of (3) in Federer 2.9.20, p. 166 The same epsilon
    and delta that bound all finite variation sums bound the induced masses
    of every open S contained in (a,b) with Lebesgue measure at most delta.
    Continuity from (3) removes the included left atoms of the selected
    dyadic cells; excluded right endpoints require no continuity. *)
Theorem absolute_continuity_open_induced_mass_bound (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b d e : R) (S : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> is_absolutely_continuous_real_curve g a b ->
  (forall t : seq (R * R), is_ordered_real_interval_family a b t ->
    (real_interval_family_length t<=d)%R -> (real_interval_family_variation_sum g t<=e)%R) ->
  open S -> S `<=` `]a,b[ -> lebesgue_scalar_measure S<=d%:E -> psip S+psim S<=e%:E.
Proof.
move=> hg hp hAC hvar hS hSub hSmall.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hP; have hmM := derivation_measure_law hM.
have hrP := derivation_measure_borel_regular hP; have hrM := derivation_measure_borel_regular hM.
pose mu A := psip A+psim A.
have hm := measure_binary_addition_is_measure hmP hmM.
have hc := real_absolute_continuity_continuous hAC.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [hOpen [hPoint _]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hg psip psim hp.
have hcell n j : measure_measurable mu (@dyadic_cell R n j).
  apply: measure_binary_addition_measurable.
  + exact: (@dyadic_cell_measurable R psip n j hmP hrP).
  + exact: (@dyadic_cell_measurable R psim n j hmM hrM).
have hU n : measure_measurable mu (@dyadic_union R S n (dyadic_bound n)).
  apply: measure_binary_addition_measurable.
  + exact: (@dyadic_union_measurable R psip S n (dyadic_bound n) hmP hrP).
  + exact: (@dyadic_union_measurable R psim S n (dyadic_bound n) hmM hrM).
have hUn n : mu (@dyadic_union R S n (dyadic_bound n))<=e%:E.
  pose t := @selected_dyadic_interval_family R S n (dyadic_bound n).
  have ht : is_ordered_real_interval_family a b t.
    exact: selected_dyadic_interval_family_ordered hSub.
  have hLen : (real_interval_family_length t<=d)%R.
    have hmu : lebesgue_scalar_measure (@dyadic_union R S n (dyadic_bound n))<=
      lebesgue_scalar_measure S.
      apply (@measure_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
        (@dyadic_union R S n (dyadic_bound n)) S)=> x [j [_ hjS hx]].
      exact: hjS x hx.
    have hh := le_trans hmu hSmall.
    by rewrite (@selected_dyadic_family_length R S n (dyadic_bound n)) lee_fin in hh.
  have hV := hvar t ht hLen.
  have hSum : mu (@dyadic_union R S n (dyadic_bound n))<=
      (real_interval_family_variation_sum g t)%:E.
    rewrite (@selected_dyadic_family_measure R mu S n (dyadic_bound n) hm (hcell n))
      /real_interval_family_variation_sum -sumEFin !big_seq.
    apply: lee_sum=> uv huv; case: uv huv=> u v huv.
    have [j [hjk [heq hCell]]] := (selected_dyadic_interval_family_member S n (dyadic_bound n) (u,v)).1 huv.
    have hu : u=@dyadic_left R n j := congr1 fst heq.
    have hv : v=(@dyadic_left R n j+@dyadic_step R n)%R := congr1 snd heq.
    have huv' : (u<v)%R by rewrite hu hv ltrDl; exact: dyadic_step_gt0.
    have hCell' : (`[u,v[ : set R) `<=` S by rewrite hu hv.
    have huIn : S u.
      apply: hCell'; by rewrite /= in_itv /= lexx huv'.
    have /andP[hau hub] : (a<u<b)%R by have := hSub u huIn; rewrite /= in_itv /=.
    have hcu := @segment_continuity_interior R g a b u hc hau hub.
    have [hPu hMu] := hPoint u hcu.
    change (is_true (mu `[u,v[<=(fine (curve_variation (g : R -> real_line_metric R) u v))%:E)).
    rewrite /mu (@measure_half_open_remove_left_atom R psip u v hmP hPu)
      (@measure_half_open_remove_left_atom R psim u v hmM hMu).
    exact: hOpen u v (ltW huv').
  apply: le_trans hSum _; by rewrite lee_fin.
have hlim := @measure_continuity_below R (real_line_metric R) mu hm
  (fun n => @dyadic_union R S n (dyadic_bound n)) hU
  (fun n m hnm => @dyadic_union_monotone_le R S n m hnm).
rewrite (@dyadic_union_open R S hS) in hlim.
exact: extended_order_limit_upper_bound hlim.2 hUn.
Qed.
