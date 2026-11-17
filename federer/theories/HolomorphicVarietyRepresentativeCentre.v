(** Federer (1969), 3.4.12, p. 339, extending the
    depth-zero case of 3.4.8(11), p. 333:
    a nonempty holomorphic variety germ contains its centre
    in every original finite-equation representative. Apply the
    existing real theorem to the original squared-modulus equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ScalarRestriction ComplexScalarSealed SetGermUP
  FiniteHolomorphicVarietyUP HolomorphicVarietyReal AnalyticVarietyRepresentativeCentre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_variety_representative_centre]: continuity
    of the original equations puts the centre in every nonempty
    variety representative, 3.4.8(11), p. 333, as extended in
    3.4.12, p. 339. *)
Theorem holomorphic_variety_representative_centre (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (U S:set X) a:
  U a ->@is_finite_holomorphic_variety R X NX hNX U S ->
  @set_germ (Topological.clone (real_norm_metric_space hNX) _) a S <>
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0 ->S a.
Proof.
move=>hUa hVariety hNonempty.
exact:(@analytic_variety_representative_centre R (restricted_space (ComplexScalars.embed R) X)
  NX hNX U S a hUa (holomorphic_variety_real_analytic hVariety) hNonempty).
Qed.
