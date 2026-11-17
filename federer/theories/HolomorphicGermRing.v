(** Federer (1969), 3.4.12, p. 339: the commutative
    ring structure on the opaque actual holomorphic-germ carrier.
    The hierarchy adapter uses only the proved public ring laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RingStructure.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:restricted_space (ComplexScalars.embed R) X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.

(** Source for [holomorphic_germ_ring]: the commutative ring
    of germs at a in 3.4.12, p. 339. This carrier
    exposes the verified ring laws and hides quotient representations. *)
Definition holomorphic_germ_ring:Type:=holomorphic_germ_space hNX a.
HB.instance Definition _:=Choice.copy holomorphic_germ_ring (holomorphic_germ_space hNX a).
HB.instance Definition _:=GRing.isZmodule.Build holomorphic_germ_ring
  (@holomorphic_germ_add_associative R X NX hNX a)
  (@holomorphic_germ_add_commutative R X NX hNX a)
  (@holomorphic_germ_add_zero R X NX hNX a)
  (@holomorphic_germ_add_negate R X NX hNX a).
HB.instance Definition _:=@GRing.Zmodule_isComNzRing.Build holomorphic_germ_ring
  (@holomorphic_germ_one R X NX hNX a) (@HolomorphicGerms.mul R X NX hNX a)
  (@holomorphic_germ_multiply_associative R X NX hNX a)
  (@holomorphic_germ_multiply_commutative R X NX hNX a)
  (@holomorphic_germ_multiply_one R X NX hNX a)
  (@holomorphic_germ_distributive R X NX hNX a)
  (@holomorphic_germ_one_not_zero R X NX hNX a).
End RingStructure.
