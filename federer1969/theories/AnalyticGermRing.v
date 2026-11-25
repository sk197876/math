(** Federer (1969), 3.4.5, p. 319: the commutative
    ring structure on the opaque actual analytic-germ carrier.
    The hierarchy adapter uses only the proved public ring laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RingStructure.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.

(** Source for [analytic_germ_ring]: the commutative ring
    of germs at a in 3.4.5, p. 319. This carrier
    exposes the verified ring laws and hides quotient representations. *)
Definition analytic_germ_ring:Type:=analytic_germ_space hNX a.
HB.instance Definition _:=Choice.copy analytic_germ_ring (analytic_germ_space hNX a).
HB.instance Definition _:=GRing.isZmodule.Build analytic_germ_ring
  (@analytic_germ_add_associative R X NX hNX a)
  (@analytic_germ_add_commutative R X NX hNX a)
  (@analytic_germ_add_zero R X NX hNX a)
  (@analytic_germ_add_negate R X NX hNX a).
HB.instance Definition _:=@GRing.Zmodule_isComNzRing.Build analytic_germ_ring
  (@analytic_germ_one R X NX hNX a) (@AnalyticGerms.mul R X NX hNX a)
  (@analytic_germ_multiply_associative R X NX hNX a)
  (@analytic_germ_multiply_commutative R X NX hNX a)
  (@analytic_germ_multiply_one R X NX hNX a)
  (@analytic_germ_distributive R X NX hNX a)
  (@analytic_germ_one_not_zero R X NX hNX a).
End RingStructure.
