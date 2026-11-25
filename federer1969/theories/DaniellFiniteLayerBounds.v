(** Federer (1969), proof of 2.5.2, p. 93: the displayed sandwich obtained
    by summing the consecutive layer inequalities from 1 to n. The formal
    induction includes the empty sum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLayers
  MonotoneDaniellIntegralUP DaniellCoverUP DaniellCoverMeasure DaniellLayerAdditivity DaniellLayerZero
  DaniellLayerIntegralBounds DaniellTruncationGrid SummableRealFunctionUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_finite_layer_integral_bounds]: the summed inequality
    of Federer 2.5.2, p. 93 Finite functional values bound the middle
    integral without a finite-measure hypothesis. *)
Theorem daniell_finite_layer_integral_bounds (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) (e : R) :
  positive_function_lattice L f -> (0 < e)%R -> forall n,
  (A (real_lattice_layer f (real_step_ceiling e 2) (real_step_ceiling e n.+1.+1)))%:E <=
    measure_lower_integral mu (real_total_integrand
      (real_lattice_layer f (real_step_ceiling e 1) (real_step_ceiling e n.+1))) /\
  measure_lower_integral mu (real_total_integrand
      (real_lattice_layer f (real_step_ceiling e 1) (real_step_ceiling e n.+1))) <=
    (A (real_lattice_layer f (real_step_ceiling e 0) (real_step_ceiling e n)))%:E.
Proof.
move=> hf he.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
have hp n : (0 <= real_step_ceiling e n)%R := real_step_ceiling_nonnegative n (ltW he).
have hnext n : (real_step_ceiling e n < real_step_ceiling e n.+1)%R := real_step_ceiling_strict_next n he.
elim=> [|n [ihlow ihup]].
- rewrite (@daniell_layer_same_functional R X L A hA f (real_step_ceiling e 2) hf.1)
    (@real_lattice_layer_same_integral R X mu hmeasure f (real_step_ceiling e 1))
    (@daniell_layer_same_functional R X L A hA f (real_step_ceiling e 0) hf.1).
  by split.
- have hstep := @daniell_consecutive_layer_integral_bounds R X L A hL hA mu hm f
    (real_step_ceiling e n) (real_step_ceiling e n.+1) (real_step_ceiling e n.+1.+1)
    (real_step_ceiling e n.+1.+1.+1) hf (hp n) (hnext n) (hnext n.+1) (hnext n.+1.+1).
  have hw1 : (real_step_ceiling e n.+1-real_step_ceiling e n=
      real_step_ceiling e n.+1.+1-real_step_ceiling e n.+1)%R by rewrite !real_step_ceiling_difference.
  have hw2 : (real_step_ceiling e n.+1.+1-real_step_ceiling e n.+1=
      real_step_ceiling e n.+1.+1.+1-real_step_ceiling e n.+1.+1)%R by rewrite !real_step_ceiling_difference.
  have [hlo hup] := hstep hw1 hw2.
  have h02 : (real_step_ceiling e 2 <= real_step_ceiling e n.+1.+1)%R.
    apply: real_step_ceiling_monotone he _; exact: leq0n.
  have h01 : (real_step_ceiling e 1 <= real_step_ceiling e n.+1)%R.
    apply: real_step_ceiling_monotone he _; exact: leq0n.
  have h00 : (real_step_ceiling e 0 <= real_step_ceiling e n)%R.
    apply: real_step_ceiling_monotone he _; exact: leq0n.
  have eI := @daniell_layer_integral_add R X L A hL hA mu hm f
    (real_step_ceiling e 1) (real_step_ceiling e n.+1) (real_step_ceiling e n.+1.+1)
    hf.1 (hp 1%N) h01 (ltW (hnext n.+1)).
  have eLo := @daniell_layer_functional_add R X L A hL hA f
    (real_step_ceiling e 2) (real_step_ceiling e n.+1.+1) (real_step_ceiling e n.+1.+1.+1)
    hf.1 (hp 2%N) h02 (ltW (hnext n.+1.+1)).
  have eUp := @daniell_layer_functional_add R X L A hL hA f
    (real_step_ceiling e 0) (real_step_ceiling e n) (real_step_ceiling e n.+1)
    hf.1 (hp 0%N) h00 (ltW (hnext n)).
  rewrite eI eLo eUp !EFinD; split.
  + exact: leeD ihlow hlo.
  + exact: leeD ihup hup.
Qed.
