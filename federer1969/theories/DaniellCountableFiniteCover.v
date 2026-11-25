(** Federer (1969), 2.5.3, p. 94, third further condition, with the proof
    instruction on p. 95. Both implications are proved here using the
    suiting envelope and actual integral witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellCoverUP LatticeSeriesCoverUP
  LatticeSeriesCoverLaws FiniteCoverSuitingSequence LatticeSeriesFiniteCover
  RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_countably_finite_series_iff]: direct third further
    condition of Federer 2.5.3, p. 94 Zero in L covers the empty-set
    boundary. No summability of the whole series is imposed; its nonnegative
    sum can be infinite. *)
Theorem daniell_countably_finite_series_iff (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (hc : is_daniell_cover_envelope L A mu)
    (T : set X) : L (fun _ => 0%R) ->
  (is_countably_finite_measure_set mu T <-> exists f, is_positive_lattice_series_cover L T f).
Proof.
move=> h0; split.
- move=> hT; have [f hf] := @countably_finite_set_daniell_suiting R X L A hL mu hm hc T h0 hT.
  exists f; exact: (daniell_suiting_series_cover hf).
- move=> [f hf]; exact: (@positive_lattice_series_countably_finite R X L A mu hm hA T f hf).
Qed.
