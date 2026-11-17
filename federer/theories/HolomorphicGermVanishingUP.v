(** Federer (1969), 3.4.12, p. 339: the
    ideal of an original set germ is specified by local
    vanishing of actual holomorphic representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric GermVanishingUP HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermOperationsUP SetGermUP GermVanishingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_set_ideal]: the independent
    membership law of ideal gamma_a(S), 3.4.12,
    p. 339. It requires the original local vanishing
    condition for every holomorphic and set representative. *)
Record is_holomorphic_set_ideal (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (I:set (holomorphic_germ_space hNX a)):Prop:={
  (** Source for [holomorphic_set_ideal_membership]: a germ
      lies in the ideal exactly when each representative
      vanishes locally on the represented set, 3.4.12, p. 339. *)
  holomorphic_set_ideal_membership:forall alpha,I alpha <->
    forall (f:@holomorphic_representative_type R X NX hNX a)
      (S:set (Topological.clone (real_norm_metric_space hNX) _)),
      holomorphic_germ f=alpha ->@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=sigma ->
      @vanishes_near_on (Topological.clone (real_norm_metric_space hNX) _) [the zmodType of (ComplexScalars.C R)^o] a S (holomorphic_representative_value f)
}.
