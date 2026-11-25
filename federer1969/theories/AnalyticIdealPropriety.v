(** Federer (1969), 3.4.5, p. 320: a
    set-germ ideal is proper exactly when the original set
    germ is nonempty. This exposes the empty-germ convention
    in the printed irreducibility/prime-ideal assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP SetGermOrder SetGermBoundary
  GermVanishingSealed AnalyticZeroGermIdeal AnalyticZeroGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_ideal_contains_one]: the unit
    vanishes locally on S exactly when S has empty
    germ, supporting 3.4.5, p. 320. *)
Lemma analytic_set_ideal_contains_one (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @AnalyticSetIdeal.value R X NX hNX a sigma (@analytic_germ_one R X NX hNX a) <->
  sigma=@set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0.
Proof.
rewrite analytic_zero_germ_ideal_equivalence analytic_zero_germ_one;split.
- exact:set_germ_subset_empty.
- move=>->;exact:set_germ_subset_reflexive.
Qed.
