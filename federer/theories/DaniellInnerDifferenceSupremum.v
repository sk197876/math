(** Federer (1969), 2.5.3, p. 94, first further condition, proof p. 95. The
    family below is exactly Federer's closed unit level minus an F1 set; it
    is not replaced by the smaller family of closed levels alone. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies DaniellInnerDifferenceApproximation
  DaniellCoverUP RealIntegralFunctionalUP MeasureUP MeasureBasic ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_inner_difference_values]: exact set of
    numbers in the first further condition of Federer 2.5.3, p. 94 *)
Definition function_lattice_inner_difference_values (R : realType) (X : Type)
    (L : set (X -> R)) (mu : set X -> \bar R) (A : set X) :=
  [set a | exists (h : X -> R) (E : set X), positive_function_lattice L h /\
    function_lattice_increasing_levels L E /\
    [set x | (1 <= h x)%R] `\` E `<=` A /\
    a=mu ([set x | (1 <= h x)%R] `\` E)].

(** Source for [daniell_inner_difference_supremum]: complete first further
    condition of Federer 2.5.3, p. 94, proof p. 95 The supremum is specified
    by its upper-bound and leastness laws. *)
Theorem daniell_inner_difference_supremum (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu) (A : set X) :
  measure_measurable mu A -> mu A < +oo ->
  is_extended_real_supremum (function_lattice_inner_difference_values L mu A) (mu A).
Proof.
move=> hA hfin; constructor.
- move=> a [h [E [hh [hE [hKA ->]]]]]; exact: (@measure_mono R X mu hm _ A hKA).
- move=> b hb; apply/lee_addgt0Pr=> e he.
  pose d := (e/3)%R.
  have hd : (0 < d)%R by rewrite /d divr_gt0 // ltr0n.
  have [h [E [hh [hE [hKA [hK hbound]]]]]] :=
    @daniell_inner_difference_approximation R X L F hL mu hm hF hc A d hA hfin hd.
  have hk : mu ([set x | (1 <= h x)%R] `\` E) <= b.
    apply: hb; exists h,E; split=> //; split=> //; by split.
  have hed : (d+(d+d))%R=e.
    rewrite -mulr2n -mulrS -(@mulr_natr R d 3) /d divfK //.
    by rewrite pnatr_eq0.
  rewrite hed in hbound; exact: le_trans hbound (leeD hk (lexx _)).
Qed.
