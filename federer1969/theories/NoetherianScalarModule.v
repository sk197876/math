(** Federer (1969), 3.4.7, p. 325: the
    first finite-module case identifies submodules of the ring
    with its ideals. This supports the induction on the
    number of module generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP RingSubmoduleUP NoetherianModuleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_submodule_ideal]: a submodule of
    the scalar ring is precisely an ideal, supporting
    the module argument of 3.4.7, p. 325. *)
Lemma scalar_submodule_ideal (A:comNzRingType) (M:set A):
  @is_ring_submodule A A^o M <->is_commutative_ideal M.
Proof.
split=>h;constructor.
- exact:ring_submodule_zero h.
- exact:ring_submodule_add h.
- exact:ring_submodule_opp h.
- exact:ring_submodule_scale h.
- exact:commutative_ideal_zero h.
- exact:commutative_ideal_add h.
- exact:commutative_ideal_opp h.
- exact:commutative_ideal_mul h.
Qed.

(** Source for [noetherian_scalar_module]: the ring
    itself is a Noetherian module when its ideals have
    finite generators, supporting 3.4.7, p. 325. *)
Theorem noetherian_scalar_module (A:comNzRingType):
  is_noetherian_commutative_ring A ->is_noetherian_ring_module A^o.
Proof.
move=>hA M hM;have [F hF]:=hA M ((@scalar_submodule_ideal A M).1 hM).
exists F;constructor;first exact:hM.
- exact:generated_commutative_ideal_contains hF.
- move=>N hN hFN.
  exact:(generated_commutative_ideal_minimal hF ((@scalar_submodule_ideal A N).1 hN) hFN).
Qed.
