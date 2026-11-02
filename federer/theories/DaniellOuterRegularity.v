(** Federer (1969), 2.5.3, pp. 94–95: outer approximation by level unions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP
  DaniellCoverUP DaniellOuterApproximation RealIntegralFunctionalUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cover_lattice_outer_regular]: Supporting Federer
    2.5.3, pp. 94–95.Sets of infinite measure are included; the definition
    is not restricted to finite hulls. *)
Theorem daniell_cover_lattice_outer_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hc : is_daniell_cover_envelope L A mu) : is_function_lattice_outer_regular L mu.
Proof.
split.
- move=> S hS; split.
  + exact: (@represented_lattice_strict_level_measurable R X L A mu hm hA S hS).
  + exact: (@represented_lattice_strict_level_finite R X L A mu hm hA S hS).
- split.
  + move=> S V hSV hV; exact: (@measure_mono R X mu hm S V hSV).
  + move=> S b hb.
    have hnon := @measure_nonnegative R X mu hm S.
    case he: (mu S)=> [m| |]; last by move: hnon; rewrite he.
    2: exact: leey.
    apply/lee_addgt0Pr=> e he0.
    have hstrict : mu S < (m+e)%R%:E by rewrite he lte_fin ltrDl.
    have [V [hSV [hV hbound]]] := @daniell_finite_outer_approximation R X L A mu hm hA hc S (m+e)%R hstrict.
    rewrite -EFinD; exact: le_trans (hb V hSV hV) hbound.
Qed.
