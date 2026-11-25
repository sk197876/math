(** Federer (1969), 4.1.4, pp. 348–349: a directed
    open exhaustion eventually contains each compact support.
    This adapter reuses the earlier compact finite-cover and
    directed finite-upper-bound theorems. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactInverseSystemUP DirectedFiniteUpperBounds CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [directed_open_compact_capture]: the implicit
    finite-cover inference for compact test supports in
    Federer 4.1.4, pp. 348–349. The compact set may be empty. *)
Theorem directed_open_compact_capture (T:topologicalType)
    (I:choiceType) (le:I->I->Prop) (hD:is_directed_preorder le)
    (O:I->set T) (K:set T):
  compact K ->(forall i,open (O i)) ->
  (forall i j,le i j ->O i `<=` O j) ->
  (forall x,K x ->exists i,O i x) ->
  exists i,K `<=` O i.
Proof.
move=>hK hOpen hMono hCover.
have hUnion:K `<=` \bigcup_(i in setT) O i.
  move=>x hx; have[i hi]:=@hCover x hx; exists i=>//.
have[F hF hCovered]:=@compact_open_finite_cover T I setT O K hK
  (fun i _=>hOpen i) hUnion.
have[i0 _]:=directed_preorder_nonempty hD.
have[k [_ hUpper]]:=@directed_finite_upper_bound I le hD i0 F.
exists k=>x hx.
have[i hi hxi]:=hCovered x hx.
exact:(@hMono i k (hUpper i hi) x hxi).
Qed.
