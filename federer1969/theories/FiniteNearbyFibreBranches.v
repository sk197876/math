(** Federer (1969), 3.4.8(10), p. 332:
    disjoint local inverse charts exhaust all
    sufficiently nearby fibres. The compact
    residual-image argument already proved in
    2.10.26 supplies the common neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteFibreEnumerationUP ProperFibreContainmentNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_nearby_fibre_branches]:
    the original nu local inverses list
    every point of each sufficiently nearby
    fibre, 3.4.8(10), p. 332.
    Compactness excludes additional branches. Local
    charts, their disjointness and the initial
    fibre cover are supplied separately. *)
Theorem finite_nearby_fibre_branches (R:realType) (X Y:metricType R)
    (I:finType) (P:X->Y) (Z:set X) (C:set Y) (y:Y)
    (U:I->set X) (V:I->set Y) (psi:I->Y->X):
  continuous P ->nbhs y C ->compact [set x|Z x /\C (P x)] ->
  (forall i,open (U i)) ->(forall i,nbhs y (V i)) ->
  (forall i z,V i z ->Z (psi i z) /\U i (psi i z) /\P (psi i z) = z) ->
  (forall i x,Z x ->U i x ->V i (P x) ->psi i (P x) = x) ->
  (forall i j,i!=j ->forall x,U i x ->~U j x) ->
  (forall x,Z x ->P x = y ->exists i,U i x) ->
  nbhs y [set z|is_finite_fibre_enumeration P Z z (fun i=>psi i z)].
Proof.
move=>hP hC hCompact hU hV hMaps hLocalInverse hDisjoint hCover.
pose O:set X:=\bigcup_(i in @setT I) U i.
have hOpen:open O by apply:bigcup_open=>i _;exact:hU i.
have hCoverO x:Z x ->P x = y ->O x.
  move=>hx hPx;have [i hi]:=hCover x hx hPx;by exists i.
have hContainment:=@proper_fibre_containment_neighbourhood R X Y P Z O C y
  hP hC hCompact hOpen hCoverO.
have hAllV:nbhs y [set z|forall i,V i z].
  exact:(@filter_forall Y I V (nbhs y) (nbhs_filter y) hV).
apply:filterS (filterI hContainment hAllV)=>z [[hc hCovered] hzV].
have hAt i:=hMaps i z (hzV i).
split.
- move=>i;split;[exact:(hAt i).1|exact:(hAt i).2.2].
split.
- move=>x hx hPx.
  have [i _ hi]:=hCovered x hx hPx.
  have hVAt:V i (P x) by rewrite hPx;exact:hzV i.
  exists i;rewrite -hPx;exact:hLocalInverse i x hx hi hVAt.
- move=>i j hEqual.
  case:(eqVneq i j)=>[hIJ|hIJ];first exact:hIJ.
  exfalso;apply:(hDisjoint i j hIJ (psi i z) (hAt i).2.1).
  by rewrite hEqual;exact:(hAt j).2.1.
Qed.
