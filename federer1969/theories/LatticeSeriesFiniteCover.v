(** Federer (1969), 2.5.3, p. 94, third further condition: a series cover
    implies a countable finite-measure cover. We cover each positive support
    by strict levels with reciprocal positive thresholds; all those levels
    have finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  LatticeSeriesCoverUP LatticeSeriesCoverLaws RealIntegralFunctionalUP MeasureUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_lattice_series_countably_finite]: series-to-cover
    implication in Federer 2.5.3, p. 94 Regularity is unnecessary for this
    direction: every representing measure makes the required positive strict
    levels finite. *)
Theorem positive_lattice_series_countably_finite (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (T : set X) (f : nat -> X -> R) :
  is_positive_lattice_series_cover L T f -> is_countably_finite_measure_set mu T.
Proof.
move=> hf.
pose V (p : nat * nat) := [set x | (((p.2.+1)%:R)^-1 < f p.1 x)%R].
pose F := V @` (setT : set (nat * nat)).
exists F; split.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
- split.
  + move=> B [p _ <-].
    apply: (@represented_lattice_strict_level_finite R X L A mu hm hA (V p)).
    exists (f p.1),(((p.2.+1)%:R)^-1)%R; split; first exact: hf.1 p.1.
    split; last by [].
    by rewrite invr_gt0 ltr0n.
  + move=> x hx; have [n hn] := positive_lattice_series_cover_positive_term hf hx.
    have [k hk] := positive_reciprocal_nat_small hn.
    exists (V (n,k)); last exact hk.
    by exists (n,k).
Qed.
