(** General topology supporting the selected-ball sequence in
    Federer (1969), 3.1.20, pp. 232–233. Univalent indexing
    preserves local finiteness; inactive slots are empty sets. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountablePartialEnumeration LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_enumeration_locally_finite]: the countable
    indexing of the locally finite ball family in Federer 3.1.20,
    pp. 232–233. Only finitely many active indices can meet a
    neighbourhood whose intersecting center set is finite. *)
Lemma partial_enumeration_locally_finite (X:topologicalType) (J:choiceType)
    (U:set X) (S:set J) (F:J->set X) eta :
  is_countable_partial_enumeration S eta -> is_locally_finite_family_on U S F ->
  @is_locally_finite_family_on X [the choiceType of (nat:Type)] U setT
    (fun i=>if eta i is Some s then F s else set0).
Proof.
move=>he hLF x hx.
have [O [hO [hxO hfin]]]:=hLF x hx.
pose M:=S `&` [set s|exists y,O y /\ F s y].
have hMS:M `<=` S by move=>s hs; exact hs.1.
have hI:=partial_enumeration_finite_inverse he hMS hfin.
exists O; split=>//; split=>//.
apply: sub_finite_set hI=>i [_ [y [hy hFy]]].
case hi:(eta i)=>[s|] in hFy; last by case:hFy.
exists s; split=>//; split.
- exact (@partial_enumeration_members J S eta he i s hi).
- by exists y.
Qed.
