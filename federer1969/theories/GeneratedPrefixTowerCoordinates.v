(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: adjacent simple prefix extensions retain exactly
    the original remaining coordinate generators. This scalar-independent
    induction uses the existing least-subring and image laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationSealed CommutativeRingImageQuotient CommutativeSubringPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [generated_prefix_tower_coordinates]: the original
    prefix coefficients and original suffix classes generate the full
    quotient, supporting 3.4.12, p. 339. Every adjacent
    generator equation and the actual full-prefix surjection remain. *)
Theorem generated_prefix_tower_coordinates n m (hMN:(m<=n)%N) (A:nat->comNzRingType) (C:comNzRingType)
    (F:forall p,(p<=n)%N ->{rmorphism A p->C}) (x:'I_n->C):
  (forall j:'I_n,(m<=j)%N ->forall (D:comNzRingType) (inclusion:{rmorphism D->C}),
    is_commutative_subring_realisation (fun y:C=>exists a:A (j:nat).+1,y=F (j:nat).+1 (ltn_ord j) a) inclusion ->
    exists scalar:{rmorphism A (j:nat)->D},exists coordinate:D,
      (forall a:A (j:nat),inclusion (scalar a)=F (j:nat) (leq_trans (leqnSn (j:nat)) (ltn_ord j)) a) /\
      inclusion coordinate=x j /\
      is_generated_commutative_subring (fun d:D=>d=coordinate \/exists a:A (j:nat),d=scalar a) setT) ->
  (forall c:C,exists a:A n,F n (leqnn n) a=c) ->
  is_generated_commutative_subring
    (fun y:C=>(exists a:A m,y=F m hMN a) \/exists j:'I_n,(m<=j)%N /\y=x j) setT.
Proof.
move=>hStep0 hFull.
constructor.
- by constructor.
- by move=>y _.
- move=>N hN hGenerators c _.
  pose Property:=fun p=>forall (hPN:(p<=n)%N) (a:A p),N (F p hPN a).
  have hTower r:Property (m+r)%N.
    elim:r=>[|r IH].
    + rewrite addn0 /Property=>hPN a.
      apply:hGenerators;left;exists a.
      by rewrite (bool_irrelevance hPN hMN).
    + rewrite addnS /Property=>hPN a.
      pose j:'I_n:=Ordinal hPN.
      pose S:set C:=fun y=>exists b:A (m+r).+1,y = F (m+r).+1 hPN b.
      have hS:is_commutative_subring S:=commutative_ring_image_subring (F (m+r).+1 hPN).
      pose D:=@CommutativeSubringRealisation.space C S hS.
      pose inclusion:=@CommutativeSubringRealisation.inclusion C S hS.
      have hImage:=@CommutativeSubringRealisation.laws C S hS.
      have hImageStep:is_commutative_subring_realisation
        (fun y:C=>exists b:A (j:nat).+1,y = F (j:nat).+1 (ltn_ord j) b) inclusion.
        have hSets:S = (fun y:C=>exists b:A (j:nat).+1,y = F (j:nat).+1 (ltn_ord j) b).
          by rewrite /S (bool_irrelevance hPN (ltn_ord j)).
        by rewrite -hSets.
      have hJTail:(m<=j)%N by rewrite /j /= leq_addr.
      have [scalar [coordinate [hScalar [hCoordinate hGenerated]]]]:=hStep0 j hJTail D inclusion hImageStep.
      have hPre:=commutative_subring_ring_preimage inclusion hN.
      have hAll:setT `<=` inclusion @^-1` N.
        apply:(generated_commutative_subring_minimal hGenerated hPre)=>d [->|[b ->]].
        * change (N (inclusion coordinate));rewrite hCoordinate.
          apply:hGenerators;right;exists j;split;last by [].
          by rewrite /j /= leq_addr.
        * change (N (inclusion (scalar b)));rewrite hScalar.
          have hPrevious:=IH (leq_trans (leqnSn (j:nat)) (ltn_ord j)) b.
          exact:hPrevious.
      have hMember:S (F (m+r).+1 hPN a) by exists a.
      have [d hD]:=(commutative_subring_inclusion_image hImage _).1 hMember.
      have hResult:=hAll d Logic.I;change (N (inclusion d)) in hResult.
      by rewrite hD in hResult.
  have hEnd:(m+(n-m)=n)%N:=subnKC hMN.
  have hLast:=hTower (n-m)%N;rewrite hEnd in hLast.
  have [beta hBeta]:=hFull c.
  have hResult:=hLast (leqnn n) beta.
  by rewrite hBeta in hResult.
Qed.
