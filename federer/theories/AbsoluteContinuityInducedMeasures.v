(** Federer (1969), 2.9.20, p. 166: (3) implies (4). The finite-family law
    gives continuity; open outer approximation transfers the small-open-set
    estimate to arbitrary Lebesgue-null sets. The selected dyadic
    finite-union proof is recorded in AbsoluteContinuityOpenMeasureBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  StieltjesDerivationClass MeasureDerivationContext ScalarIntervalDerivationContext
  RealAbsoluteContinuityUP RealAbsoluteContinuityBasic AbsoluteContinuityFamilyVariation
  AbsoluteContinuityOpenMeasureBound DerivationNullOpenCover LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureRestriction MeasureAbsoluteContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_absolute_continuity_induced_measures]: direct
    implication (3)=>(4) of Federer 2.9.20, p. 166 Each arbitrary null set
    in (a,b) is covered by an open subset of that interval of arbitrarily
    small Lebesgue measure. The established open-set mass bound forces the
    sum of both restricted induced measures to vanish; nonnegativity gives
    the two absolute-continuity laws. Continuity is relative to the closed
    segment, including endpoints. *)
Theorem real_absolute_continuity_induced_measures (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> is_absolutely_continuous_real_curve g a b ->
  real_curve_continuous_induced_measures g psip psim a b.
Proof.
move=> hg hp hAC; split; first exact: real_absolute_continuity_continuous hAC.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hP; have hmM := derivation_measure_law hM.
have hL := lebesgue_scalar_is_measure R.
pose U : set (real_line_metric R) := `]a,b[.
have hNull N : lebesgue_scalar_measure N=0 ->
    psip (U `&` N)=0 /\ psim (U `&` N)=0.
  move=> hN.
  have hsum : psip (U `&` N)+psim (U `&` N)=0.
    apply/eqP; rewrite eq_le (adde_ge0 (measure_nonnegative hmP _) (measure_nonnegative hmM _)) andbT.
    apply/lee_addgt0Pr=> e he; rewrite add0e.
    have [d [hd hvar]] := @real_absolute_continuity_family_variation R g a b hg hAC e he.
    have [W [hW [hNW hSmall]]] := @derivation_null_open_cover R
      [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R) N d
      (derivation_context_measure (scalar_interval_derivation_context R)) hN hd.
    pose S := W `&` U.
    have hS : open S by apply: openI hW _; exact: interval_open.
    have hSub : S `<=` `]a,b[ by move=> x [].
    have hSsmall : lebesgue_scalar_measure S<=d%:E.
      apply: le_trans _ (ltW hSmall).
      apply (@measure_mono R (real_line_metric R) (@lebesgue_scalar_measure R) hL S W).
      by move=> x [].
    have hCover : U `&` N `<=` S.
      by move=> x [hxU hxN]; split=> //; exact: hNW x hxN.
    apply: le_trans (leeD (@measure_mono R R psip hmP _ _ hCover)
      (@measure_mono R R psim hmM _ _ hCover)) _.
    exact: absolute_continuity_open_induced_mass_bound hg hp hAC hvar hS hSub hSsmall.
  split.
  - apply/eqP; rewrite eq_le (measure_nonnegative hmP _) andbT.
    rewrite -hsum; exact: lee_paddr (measure_nonnegative hmM _) (lexx _).
  - apply/eqP; rewrite eq_le (measure_nonnegative hmM _) andbT.
    rewrite -hsum; exact: lee_paddl (measure_nonnegative hmP _) (lexx _).
split; move=> N hN; [exact: (hNull N hN).1|exact: (hNull N hN).2].
Qed.
