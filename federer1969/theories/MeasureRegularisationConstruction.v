(** Federer (1969), 2.1.5, p. 57, regularisation formula. This private
    existence witness is used only by the sealing module and assumption
    audit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds MeasureUP MeasureRegularisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_regularisation_exists]: Federer
    2.1.5, p. 57, final display; the extended-real infimum witnesses
    the abstract regularisation specification. Its order laws hold
    even before assuming that the input function is a measure. *)
Lemma measure_regularisation_exists (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : exists nu, is_measure_regularisation mu nu.
Proof.
exists (fun A => extended_real_inf [set t | exists B,
  A `<=` B /\ measure_measurable mu B /\ t = mu B]).
constructor.
- move=> A B hAB hB; apply: extended_real_inf_lower.
  exists B; by split=> //; split.
- move=> A c hc; apply: extended_real_inf_greatest=> t [B [hAB [hB ->]]].
  exact: hc B hAB hB.
Qed.
