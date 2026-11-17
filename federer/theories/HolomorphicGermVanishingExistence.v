(** Federer (1969), 3.4.12, p. 339: the
    original all-representative vanishing law determines a unique
    subset of the holomorphic-germ ring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric GermVanishingUP HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermOperationsUP SetGermUP HolomorphicGermVanishingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_ideal_exists]: existence of
    the original ideal membership set, 3.4.12, p. 339.
    Its algebraic ideal laws are proved separately. *)
Theorem holomorphic_set_ideal_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  exists I:set (holomorphic_germ_space hNX a),is_holomorphic_set_ideal sigma I.
Proof.
exists (fun alpha=>forall (f:@holomorphic_representative_type R X NX hNX a)
  (S:set (Topological.clone (real_norm_metric_space hNX) _)),
  holomorphic_germ f=alpha ->@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=sigma ->
  @vanishes_near_on (Topological.clone (real_norm_metric_space hNX) _) [the zmodType of (ComplexScalars.C R)^o] a S (holomorphic_representative_value f)).
constructor=>alpha;by split.
Qed.

(** Source for [holomorphic_set_ideal_unique]: the original
    vanishing membership law is unique, 3.4.12, p. 339. *)
Lemma holomorphic_set_ideal_unique (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (I J:set (holomorphic_germ_space hNX a)):
  is_holomorphic_set_ideal sigma I ->is_holomorphic_set_ideal sigma J ->I=J.
Proof.
move=>hI hJ;apply/seteqP;split=>alpha.
- by rewrite (holomorphic_set_ideal_membership hI alpha) (holomorphic_set_ideal_membership hJ alpha).
- by rewrite (holomorphic_set_ideal_membership hI alpha) (holomorphic_set_ideal_membership hJ alpha).
Qed.
