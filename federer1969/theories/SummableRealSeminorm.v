(** Federer (1969), 2.9.23, pp. 168–169: the counterexample takes values in
    L1 with the seminorm convention of 2.4.12, pp. 86–87, rather than
    identifying functions almost everywhere. We retain the existing sealed
    total-function carrier. Chapter 21 has no counterpart of this example.
    The local Federer erratum has no entry for this example on pp. 168–169. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP MeasureUP SummableRealSpace
  TotalScalarLpFiniteSeminorm FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_real_seminorm]: supporting real-valued
    L1 seminorm for Federer 2.9.23, p. 168, defined by
    2.4.12, p. 86. Finiteness follows from membership of
    the sealed carrier; no definiteness is asserted. *)
Definition summable_real_seminorm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : summable_real_space hm) :=
  finite_total_scalar_lp_norm mu 1 (summable_real_value f).

(** Source for [summable_real_seminorm_laws]: supporting nonnegative,
    homogeneous, subadditive seminorm in Federer 2.9.23, p. 168; these are
    the defining laws of 2.4.12, p. 86. *)
Lemma summable_real_seminorm_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_seminorm (@summable_real_seminorm R X mu hm).
Proof.
have hL := @finite_total_scalar_lp_norm_laws R X mu hm 1.
constructor.
- move=> f; exact: (function_seminorm_nonnegative hL (summable_real_value_lone f)).
- move=> c f; rewrite /summable_real_seminorm linearZ /=.
  exact: (function_seminorm_scale hL c (summable_real_value_lone f)).
- move=> f g; rewrite /summable_real_seminorm linearD /=.
  exact: (function_seminorm_triangle hL (summable_real_value_lone f) (summable_real_value_lone g)).
Qed.
