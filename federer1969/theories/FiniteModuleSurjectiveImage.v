(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: finite generators pass to an
    actual surjective module image. Apply the
    existing submodule preimage theorem and the
    original least-submodule specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP RingSubmoduleLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_module_surjective_linear_image]:
    transfer a finite prefix module to its
    actual quotient image, supporting 3.4.8(8),
    p. 329. This is a connection between
    existing abstract module interfaces. *)
Theorem finite_module_surjective_linear_image (A:nzRingType) (V W:lmodType A)
  (f:{linear V->W}):
  (forall w:W,exists v:V,f v = w) ->
  is_finitely_generated_ring_submodule (setT:set V) ->
  is_finitely_generated_ring_submodule (setT:set W).
Proof.
move=>hOnto [F hF];exists (map f F);constructor.
- by constructor.
- by move=>x _.
- move=>N hN hGenerators.
  have hPre:=ring_submodule_linear_preimage f hN.
  have hAll:setT `<=` f @^-1` N.
    apply:(generated_ring_submodule_minimal hF hPre)=>v hV.
    apply:hGenerators;apply/mapP;by exists v.
  move=>w _;have [v <-]:=hOnto w;exact:hAll v Logic.I.
Qed.
