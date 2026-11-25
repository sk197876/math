(** Local boundary clarification of Federer (1969), 2.4.12, p. 86,
    phi_(infinity) defining display. Neither displayed formula explicitly
    states the range of r. If r ranges over all real numbers, the zero
    measure violates the claimed nonnegative seminorm property. The public
    specification uses nonnegative thresholds, as documented in
    MeasureEssentialNormUP.v. This clarification is separate from Federer's
    May-1987 erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureGauge ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unrestricted_essential_thresholds_fail_nonnegativity]:
    local counterexample to reading the defining infimum in
    Federer 2.4.12, p. 86, over unrestricted real
    thresholds. Under the zero measure, minus one is feasible
    regardless of the function, forcing the infimum below zero. *)
Lemma unrestricted_essential_thresholds_fail_nonnegativity (R : realType)
    (X Y : Type) (N : Y -> R) (f : partial_function X Y) :
  ~ (0 <= extended_real_inf [set r : \bar R | exists t : R,
    r=t%:E /\ (fun _ : set X => (0 : \bar R)) (partial_norm_superlevel N f r) = 0]).
Proof.
move=> hnon.
have hbound : extended_real_inf [set r : \bar R | exists t : R,
    r=t%:E /\ (fun _ : set X => (0 : \bar R)) (partial_norm_superlevel N f r) = 0] <= (-1)%:E.
  apply: extended_real_inf_lower; exists (-1)%R; by split.
have hh := le_trans hnon hbound.
by move: hh; rewrite lee_fin ler0N1.
Qed.
