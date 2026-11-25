(** General topology supporting Federer (1969), 3.2.28(4),
    pp. 266–267: exhaust a second countable manifold
    by compact subsets before applying the finite-mass
    area theorem 3.2.20, pp. 256–257. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof CountableDefaultEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_compact_neighbourhood_cover]:
    supporting compact exhaustion for the general manifold
    assertion in Federer 3.2.28(4), pp. 266–267.
    The local compact-neighbourhood and countable-base
    hypotheses are explicit and must be proved for
    the actual manifold; no compactness is assumed globally. *)
Theorem countable_compact_neighbourhood_cover (T:topologicalType)
    (B:set T) (U:nat->set T):
  is_countable_open_base U ->
  (forall b,B b ->exists V K:set T,
    open V /\V b /\compact K /\K `<=` B /\B `&` V `<=` K) ->
  exists K:nat->set T,
    (forall i,compact (K i) /\K i `<=` B) /\B=\bigcup_i K i.
Proof.
move=>hBase hLocal.
pose C:set (set T):=[set V|open V /\exists K:set T,compact K /\K `<=` B /\B `&` V `<=` K].
have hCover:B `<=` \bigcup_(V in C) V.
  move=>b hb; have [V [K [hV [hbV [hK [hKB hBK]]]]]]:=hLocal b hb.
  exists V; last exact hbV; split; first exact hV.
  exists K; by split=>//; split.
have [G [hGC [hG hBG]]]:=@countable_base_open_subcover T U B C hBase (fun V hV=>hV.1) hCover.
have hZero:C set0.
  split; first exact:open0.
  exists set0; split; first exact:compact0.
  by split=>[x []|x [_ []]].
have [u [hu hEnum]]:=countable_default_enumeration set0 hG.
have hU i:C (u i).
  case:(hu i)=>[hi|->]; last exact hZero.
  exact:hGC (u i) hi.
have hExist i:exists K:set T,compact K /\K `<=` B /\B `&` u i `<=` K:=(hU i).2.
pose K i:=projT1 (cid (hExist i)).
have hK i:=projT2 (cid (hExist i)).
exists K; split.
- move=>i; split; [exact:(hK i).1|exact:(hK i).2.1].
- apply/seteqP; split=>x.
  + move=>hx; have [V hVG hxV]:=hBG x hx.
    have [i hEq]:=hEnum V hVG.
    exists i; first exact I.
    apply:(hK i).2.2; split; first exact hx.
    by rewrite hEq.
  + move=>[i _ hx]; exact:(hK i).2.1 x hx.
Qed.
