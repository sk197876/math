(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: the original finite generator
    family remains generating when the scalar
    action factors through the preceding quotient
    ring. Apply the least-submodule law directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_module_scalar_enlargement]: pass
    from the original analytic coefficient ring
    to its quotient image in the nested
    finite extension of 3.4.8(8), p. 329.
    The scalar triangle is the original
    ring-map compatibility, not an injectivity premise. *)
Theorem finite_module_scalar_enlargement (A B C:comNzRingType)
  (original:{rmorphism A->C}) (factor:{rmorphism A->B}) (scalar:{rmorphism B->C}):
  (forall a:A,scalar (factor a) = original a) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space original C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType B of ring_restricted_space scalar C^o]).
Proof.
move=>hTriangle [F hF];exists F;constructor.
- by constructor.
- by move=>x _.
- move=>N hN hGenerators.
  have hRestricted:is_ring_submodule
      (N:set [the lmodType A of ring_restricted_space original C^o]).
    constructor.
    * exact:ring_submodule_zero hN.
    * exact:(@ring_submodule_add B _ N hN).
    * exact:(@ring_submodule_opp B _ N hN).
    * move=>a x hX;change (N (original a*x));rewrite -hTriangle.
      exact:(@ring_submodule_scale B _ N hN (factor a) x hX).
  exact:(generated_ring_submodule_minimal hF hRestricted hGenerators).
Qed.
