(** Federer (1969), 2.5.13, p. 106: the variation measures furnished by
    2.5.5 are L regular. The level families defining regularity already use
    L+, by 2.5.3, p. 94, so L regularity and L+ regularity coincide. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [function_lattice_strict_levels_positive]: supporting
    invariance of F0 under replacing L by L+ in Federer
    2.5.3, p. 94, used by 2.5.13, p. 106. *)
Lemma function_lattice_strict_levels_positive (R : realType) (X : Type) (L : set (X -> R)) :
  function_lattice_strict_levels (positive_function_lattice L) = function_lattice_strict_levels L.
Proof.
apply/seteqP; split.
- move=> S [f [t [hf [ht he]]]]; exists f,t; split; first exact hf.1.
  by split.
- move=> S [f [t [hf [ht he]]]]; exists f,t; split.
  + by split; last exact hf.2.
  + by split.
Qed.

(** Source for [function_lattice_increasing_levels_positive]:
    supporting invariance of F1 in Federer 2.5.3, p. 94,
    used in the regularity conclusion of 2.5.13, p. 106. *)
Lemma function_lattice_increasing_levels_positive (R : realType) (X : Type) (L : set (X -> R)) :
  function_lattice_increasing_levels (positive_function_lattice L) = function_lattice_increasing_levels L.
Proof. by rewrite /function_lattice_increasing_levels function_lattice_strict_levels_positive. Qed.

(** Source for [function_lattice_finite_hulls_positive]: supporting
    invariance of F2 in Federer 2.5.3, p. 94, used
    in the regularity conclusion of 2.5.13, p. 106. *)
Lemma function_lattice_finite_hulls_positive (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) :
  function_lattice_finite_hulls (positive_function_lattice L) mu = function_lattice_finite_hulls L mu.
Proof. by rewrite /function_lattice_finite_hulls function_lattice_increasing_levels_positive. Qed.

(** Source for [function_lattice_regular_positive_iff]: the
    identification of L+ regularity with L regularity used
    when applying 2.5.5 in Federer 2.5.13, p. 106.
    It follows from the definitions and needs no additional lattice laws. *)
Lemma function_lattice_regular_positive_iff (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) :
  is_function_lattice_regular (positive_function_lattice L) mu <-> is_function_lattice_regular L mu.
Proof. by rewrite /is_function_lattice_regular function_lattice_finite_hulls_positive. Qed.
