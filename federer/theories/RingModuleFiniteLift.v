(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: finite generation transfers
    along an injective linear map onto the
    original module. Apply the existing image
    submodule and least-module laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP RingSubmoduleLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ring_module_finite_injective_lift]: the
    carrier of the original finite coefficient
    subspace is finitely generated, supporting
    fraction-field finiteness in 3.4.8(8),
    pp. 329–330. All selected generator lifts
    remain local existence witnesses. *)
Theorem ring_module_finite_injective_lift (A:nzRingType) (V W:lmodType A)
  (f:{linear W->V}) (M:set V):
  injective f ->(forall v:V,M v <->exists w:W,f w = v) ->
  is_finitely_generated_ring_submodule M ->
  is_finitely_generated_ring_submodule (setT:set W).
Proof.
move=>hInjective hImage [F hF].
have hLift:forall v:V,exists w:W,v \in F ->f w = v.
  move=>v;case:(pselect (v \in F))=>hV.
  - have hM:=generated_ring_submodule_contains hF hV.
    have [w hW]:=(hImage v).1 hM;exists w;by [].
  - exists 0;move=>h;exfalso;exact:hV h.
have [lift hLiftLaw]:=choice hLift.
exists (map lift F);constructor.
- by constructor.
- by move=>w _.
- move=>N hN hGenerators w _.
  have hMapped:=@ring_submodule_linear_image A W V f N hN.
  have hContains:[set v|v \in F] `<=` f @` N.
    move=>v hV;exists (lift v).
    * apply:hGenerators;apply/mapP;by exists v.
    * exact:hLiftLaw v hV.
  have hAll:=generated_ring_submodule_minimal hF hMapped hContains.
  have hIn:M (f w) by apply:(hImage (f w)).2;exists w.
  have [u hU hEqual]:=hAll (f w) hIn.
  have hUW:u = w:=@hInjective u w hEqual;by rewrite -hUW.
Qed.
