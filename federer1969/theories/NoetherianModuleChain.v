(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: increasing submodules of a Noetherian
    module stabilise. Reuse the finite-generation
    specification of 3.4.7. The union and a finite
    bound on its generators prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP NoetherianModuleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_module_ascending_stabilizes]:
    the finite-module argument for integral dependence
    in 3.4.8(8), p. 329. This extends the
    increasing-ideal argument used in 3.4.5 to modules;
    all original submodules use their independent laws. *)
Theorem noetherian_module_ascending_stabilizes (A:nzRingType) (V:lmodType A)
  (M:nat->set V):
  is_noetherian_ring_module V ->(forall j,is_ring_submodule (M j)) ->
  (forall i j,(i<=j)%N ->M i `<=` M j) ->
  exists N,forall j,(N<=j)%N ->M j = M N.
Proof.
move=>hNoetherian hM hMono.
pose U:set V:=fun x=>exists j,M j x.
have hU:is_ring_submodule U.
  constructor.
  - exists 0%N;exact:ring_submodule_zero (hM 0%N).
  - move=>x y [i hX] [j hY];exists (maxn i j).
    exact:(@ring_submodule_add A V _ (hM (maxn i j)) x y
      (hMono i _ (leq_maxl i j) x hX) (hMono j _ (leq_maxr i j) y hY)).
  - move=>x [i hX];exists i;exact:(@ring_submodule_opp A V _ (hM i) x hX).
  - move=>a x [i hX];exists i;exact:(@ring_submodule_scale A V _ (hM i) a x hX).
have [F hF]:=hNoetherian U hU.
have hBound:forall G:seq V,(forall x,x \in G ->U x) ->
    exists j,forall x,x \in G ->M j x.
  elim=>[|x G ih] hG.
  - exists 0%N=>y;by rewrite in_nil.
  - have [i hX]:=hG x (mem_head x G).
    have hTail y (hy:y \in G):U y by apply:hG;rewrite in_cons hy orbT.
    have [j hJ]:=ih hTail.
    exists (maxn i j)=>y;rewrite in_cons;move/orP=>[/eqP ->|hY].
    + exact:hMono i _ (leq_maxl i j) x hX.
    + exact:hMono j _ (leq_maxr i j) y (hJ y hY).
have [N hN]:=hBound F (generated_ring_submodule_contains hF).
have hUN:U `<=` M N:=generated_ring_submodule_minimal hF (hM N) hN.
exists N=>j hNJ;apply/seteqP;split.
- move=>x hX;apply:hUN;by exists j.
- exact:hMono N j hNJ.
Qed.
