(** Private existence witness for Federer (1969), 2.5.2, pp. 92–93. The
    nonempty case uses the already sealed suiting-sequence envelope and its
    proved measure and representation theorems. The empty case uses the zero
    measure. our zero-measure branch supplies the omitted vacuous case.
    Downstream arguments use only the abstract laws in DaniellMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverSealed DaniellCoverMeasure DaniellSignedRepresentation
  DaniellEmptyBoundary DaniellMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_daniell_measure_exists]: existence conclusion of
    Federer 2.5.2, p. 92, with the printed construction on pp. 92–93 All
    specification fields are proved, including the original envelope formula
    in the nonempty case. *)
Theorem monotone_daniell_measure_exists (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_monotone_daniell_integral L A ->
  exists mu, is_monotone_daniell_measure L A mu.
Proof.
move=> hL hA; case: (pselect (exists f, L f))=> [hne|hempty].
- have [f hf] := hne.
  pose mu := @DaniellCover.value R X L A.
  have hm : is_daniell_cover_envelope L A mu := @DaniellCover.laws R X L A.
  exists mu; constructor.
  + exact: (@daniell_cover_is_measure R X L A hL hA mu hm (function_lattice_zero hL hf)).
  + exact: (@daniell_cover_represents_lattice R X L A hL hA mu hm).
  + by move=> _.
- exists (fun _ : set X => (0 : \bar R)); constructor.
  + exact: daniell_zero_measure.
  + move=> f hf; exfalso; apply: hempty; by exists f.
  + by move=> hne; exfalso; exact: hempty hne.
Qed.
