(** Federer (1969), 3.4.8(11), p. 334:
    the original finitely many prepared equations
    vanish on the original variety in one
    common neighbourhood. Reuse finite germ containment
    from 3.4.5 and its exact local-inclusion law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP
  SetGermUP SetGermOrder GermVanishingSealed FiniteGermVanishingContainment FiniteAnalyticVarietyUP FiniteZeroSetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ideal_equations_neighbourhood]:
    the simultaneous original W_j equations near
    zero in 3.4.8(11), p. 334. *)
Theorem finite_ideal_equations_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (J:finType)
    (f:J->@analytic_representative_type R X NX hNX a) (S:set X):
  (forall j,@AnalyticSetIdeal.value R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S) (analytic_germ (f j))) ->
  exists U:set X,@open (real_norm_metric_space hNX) U /\ U a /\
    forall j x,S x ->U x ->analytic_representative_value (f j) x = 0.
Proof.
move=>hVanish.
have hContainment:=@finite_germ_vanishing_containment R X NX hNX a J f setT S
  Logic.I openT hVanish.
have /set_germ_subset_original [U [hU [ha hZero]]]:=hContainment.
exists U;split;first exact:hU.
split;first exact:ha.
move=>j x hSx hUx.
have hEquations:=hZero x hSx hUx.
have [_ hAll]:=(original_zero_set_membership (FiniteZeroSet.laws setT
  (fun j=>analytic_representative_value (f j))) x).1 hEquations.
exact:hAll j.
Qed.
