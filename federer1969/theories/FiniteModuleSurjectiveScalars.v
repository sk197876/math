(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: a surjective scalar map
    preserves finite generation on restriction.
    Apply the original least-submodule laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_module_surjective_scalar_restriction]:
    equivalent original coefficient carriers give
    the same finite module property in
    3.4.8(8), p. 329. Only surjectivity
    and the actual scalar triangle are used. *)
Theorem finite_module_surjective_scalar_restriction (A B C:comNzRingType)
  (original:{rmorphism A->C}) (factor:{rmorphism A->B}) (scalar:{rmorphism B->C}):
  (forall a:A,scalar (factor a) = original a) ->(forall b:B,exists a:A,factor a = b) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType B of ring_restricted_space scalar C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space original C^o]).
Proof.
move=>hTriangle hOnto [F hF];exists F;constructor.
- by constructor.
- by move=>x _.
- move=>N hN hGenerators.
  have hEnlarged:is_ring_submodule
      (N:set [the lmodType B of ring_restricted_space scalar C^o]).
    constructor.
    * exact:ring_submodule_zero hN.
    * exact:(@ring_submodule_add A _ N hN).
    * exact:(@ring_submodule_opp A _ N hN).
    * move=>b x hX;have [a hA]:=hOnto b.
      change (N (scalar b*x));rewrite -hA hTriangle.
      exact:(@ring_submodule_scale A _ N hN a x hX).
  exact:(generated_ring_submodule_minimal hF hEnlarged hGenerators).
Qed.
