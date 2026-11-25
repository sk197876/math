(** Federer (1969), 3.4.12, p. 339:
    actual holomorphic variety germs are real analytic
    variety germs in the original underlying real space.
    Use the proved squared-modulus equations of the same
    original representatives and the same set-germ map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric
  SetGermUP AnalyticVarietyGermUP HolomorphicVarietyGermUP HolomorphicVarietyReal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Germs.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.

(** Source for [holomorphic_variety_germ_real]: the original
    complex variety germ is also an actual real analytic
    germ, 3.4.12, p. 339. Its centre,
    represented set and germ equality are unchanged. *)
Theorem holomorphic_variety_germ_real a
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  @is_analytic_variety_germ R XR NX hNX a alpha.
Proof.
move=>[U [S [ha [hS hGerm]]]];exists U,S;split;first exact:ha.
split;last exact:hGerm;exact:holomorphic_variety_real_analytic hS.
Qed.

(** Source for [holomorphic_set_real_analytic]: an original
    holomorphic set is real analytic on its original
    domain, supporting the real-case component argument in
    3.4.12, p. 339. *)
Theorem holomorphic_set_real_analytic (A S:set X):
  @is_holomorphic_set_in R X NX hNX A S ->@is_analytic_set_in R XR NX hNX A S.
Proof. move=>h a ha;exact:holomorphic_variety_germ_real (h a ha). Qed.
End Germs.
