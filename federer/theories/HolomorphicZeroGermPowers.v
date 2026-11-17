(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    a positive power has the same zero
    germ. Apply the existing product-zero-germ law
    of 3.4.5, p. 320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing
  SetGermUP SetGermOrder SetGermBooleanOrder HolomorphicZeroGermSealed HolomorphicZeroGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_zero_germ_positive_power]:
    removing delta's zero set allows cancellation
    of every positive delta power in the
    variety-germ argument, 3.4.8(10), p. 331. *)
Lemma holomorphic_zero_germ_positive_power (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (delta:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]) u:
  (0<u)%N ->@HolomorphicZeroGerm.value R X NX hNX a (delta^+u) =
    @HolomorphicZeroGerm.value R X NX hNX a delta.
Proof.
case:u=>[|u];first by rewrite ltn0.
move=>_;elim:u=>[|u hInduction];first by rewrite expr1.
rewrite exprS (@holomorphic_zero_germ_product R X NX hNX a) hInduction.
apply:set_germ_subset_antisymmetric.
- apply:set_germ_subset_join_bound;exact:set_germ_subset_reflexive.
- exact:set_germ_subset_join_left.
Qed.
