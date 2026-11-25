(** Federer (1969), 3.2.4, p. 244: remove the
    preimages of earlier piece images, then unite the
    remaining Borel pieces to obtain a univalent restriction. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import BorelFamilyUP TopologicalBorel BorelFamilyBasic BorelFunctionUP BorelFunctionBasic
  SetSequenceDisjointification CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_univalent_sequence_selection]: supporting
    selection argument in Federer 3.2.4, p. 244.
    Each piece has Borel image and an injective restriction.
    Removing preimages of earlier images keeps exactly one
    preimage per image point, while preserving the whole image. *)
Theorem borel_univalent_sequence_selection (X Y:topologicalType) (f:X->Y) (E:nat->set X):
  is_borel_function f -> (forall i,borel_set (E i)) ->
  (forall i,forall x y,E i x -> E i y -> f x=f y -> x=y) ->
  (forall i,borel_set (f @` E i)) ->
  exists B,borel_set B /\ B `<=` \bigcup_i E i /\
    (forall x y,B x -> B y -> f x=f y -> x=y) /\
    f @` B=f @` (\bigcup_i E i).
Proof.
move=>hf hE hInj hImage.
pose F i:=f @` E i.
pose D i:=set_sequence_disjointify F i.
pose P i:=E i `&` (f @^-1` D i).
pose B:=\bigcup_i P i.
have hDB i:borel_set (D i).
  apply:borel_set_difference; first exact (hImage i).
  apply:borel_set_countable_union; first exact:countableP.
  by move=>j _; exact (hImage j).
have hPB i:borel_set (P i).
  exact (borel_family_binary_intersection (borel_sets_family X) (hE i)
    (borel_function_preimage hf (hDB i))).
have hImageP i:f @` P i=D i.
  apply/seteqP; split=>y.
  - by move=>[x [_ hx] <-].
  - move=>hy; have [x hx hxy]:=hy.1; exists x.
    + split; first exact hx.
      change (D i (f x)); by rewrite hxy.
    + exact hxy.
have hSubset:B `<=` \bigcup_i E i.
  by move=>x [i _ [hx _]]; exists i.
exists B; split.
- apply:borel_set_countable_union; first exact:countableP.
  by move=>i _; exact (hPB i).
split; first exact hSubset; split.
- move=>x y [i _ [hxi hDx]] [j _ [hyj hDy]] he.
  have [hij|hij]:=eqVneq i j.
  + subst j; exact (hInj i x y hxi hyj he).
  + exfalso; apply:(@set_sequence_disjointify_disjoint Y F i j hij (f x) hDx).
    by rewrite he.
- apply/seteqP; split=>y.
  + move=>[x hx hxy]; exists x; first exact (hSubset x hx); exact hxy.
  + move=>[x [i _ hxi] hxy].
    have hy:(\bigcup_i F i) y by exists i=>//; exists x.
    rewrite -set_sequence_disjointify_union in hy.
    have [j _ hj]:=hy; change (D j y) in hj.
    rewrite -(hImageP j) in hj.
    have [z hz hzy]:=hj; exists z; first by exists j.
    exact hzy.
Qed.

(** Source for [borel_univalent_countable_selection]: countable
    Borel-family form of the construction in Federer 3.2.4,
    p. 244. The empty family and empty domain are included. *)
Theorem borel_univalent_countable_selection (X Y:topologicalType) (f:X->Y) (G:set (set X)):
  is_borel_function f -> countable G ->
  (forall E,G E -> borel_set E) ->
  (forall E,G E -> forall x y,E x -> E y -> f x=f y -> x=y) ->
  (forall E,G E -> borel_set (f @` E)) ->
  exists B,borel_set B /\ B `<=` \bigcup_(E in G) E /\
    (forall x y,B x -> B y -> f x=f y -> x=y) /\
    f @` B=f @` (\bigcup_(E in G) E).
Proof.
move=>hf hG hB hI hIm.
case:(pselect (exists E,G E))=>[hNonempty|hEmpty].
- have [E hRange]:=countable_nonempty_family_enumeration (fun E:set X=>E) hG hNonempty.
  have hMember i:G (E i).
    have hi:(E @` setT) (E i) by exists i.
    rewrite hRange in hi; by have [C hC <-]:=hi.
  have hUnion:(\bigcup_i E i)=\bigcup_(C in G) C.
    apply/seteqP; split=>x.
    + move=>[i _ hx]; exists (E i)=>//; exact (hMember i).
    + move=>[C hC hx].
      have hc:((fun C:set X=>C) @` G) C by exists C.
      rewrite -hRange in hc; have [i _ hi]:=hc; exists i=>//; by rewrite hi.
  have [B [hb [hSub [hi him]]]]:=borel_univalent_sequence_selection hf
    (fun i=>hB (E i) (hMember i)) (fun i=>hI (E i) (hMember i))
    (fun i=>hIm (E i) (hMember i)).
  exists B; by rewrite -hUnion; split=>//; split=>//; split.
- have hUnion:(\bigcup_(E in G) E)=set0.
    apply/seteqP; split=>x; last by case.
    move=>[E hE hx]; exfalso; apply:hEmpty; by exists E.
  rewrite hUnion; exists set0; split; first exact:(borel_family_empty (borel_sets_family X)).
  split; first by move=>x [].
  split; first by move=>x y [].
  by [].
Qed.
