(** The auxiliary class Q in Federer (1969), proof of 2.8.4, p. 143: unions
    of chains remain eligible, and a sufficiently large remaining set may be
    adjoined. These consequences use only the abstract saturation laws.
    Source context and corrected nonempty-member condition:
    WeightedCoverSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import CountablyClosedFamilyUP WeightedCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_weight_saturated_family]: the empty disjointed family
    belongs to Q in Federer 2.8.4, p. 143 *)
Lemma empty_weight_saturated_family (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) :
  is_weight_saturated_family F d tau set0.
Proof. constructor; [by move=> T []|by move=> T S []|by move=> T S hT []]. Qed.

(** Source for [chain_union_weight_saturated]: closure of Q under chain
    unions, implicit in Federer 2.8.4, p. 143, and proved. No countability
    condition is placed on the chain. *)
Lemma chain_union_weight_saturated (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (C : set (set (set X))) :
  (forall H, C H -> is_weight_saturated_family F d tau H) ->
  (forall H K, C H -> C K -> H `<=` K \/ K `<=` H) ->
  is_weight_saturated_family F d tau (\bigcup_(H in C) H).
Proof.
move=> hs hc; constructor.
- move=> T [H hH ht]; exact (@saturated_family_members R X F d tau H (hs H hH) T ht).
- move=> T S [H hH ht] [K hK hsk] hne.
  have [hHK|hKH] := hc H K hH hK.
  * exact (@saturated_family_disjoint R X F d tau K (hs K hK) T S (hHK T ht) hsk hne).
  * exact (@saturated_family_disjoint R X F d tau H (hs H hH) T S ht (hKH S hsk) hne).
- move=> T S hT [H hH hsH] hmeet.
  have [U [hU hb]] := @saturated_family_controls_intersections R X F d tau H
    (hs H hH) T S hT hsH hmeet.
  exists U; split=> //; by exists H.
Qed.

(** Source for [saturated_family_insert_large_remaining]: adjoining W to G
    preserves Q when W is disjoint from every old member and its scaled
    weight bounds every remaining eligible weight, Federer 2.8.4, p. 143
    Nonemptiness of W is used later in the maximality contradiction, not in
    this step. *)
Lemma saturated_family_insert_large_remaining (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (G : set (set X)) (W : set X) :
  is_weight_saturated_family F d tau G -> F W ->
  (forall S, G S -> W `&` S = set0) ->
  (forall T, F T -> (forall S, G S -> T `&` S = set0) -> d T <= tau * d W) ->
  is_weight_saturated_family F d tau (G `|` [set W]).
Proof.
move=> hG hW hdis hlarge; constructor.
- move=> T [hT|->]; last exact hW.
  exact (@saturated_family_members R X F d tau G hG T hT).
- move=> T S [ht|->] [hs|->] hne.
  * exact (@saturated_family_disjoint R X F d tau G hG T S ht hs hne).
  * rewrite setIC; exact: hdis.
  * exact: hdis.
  * exfalso; apply: hne; reflexivity.
- move=> T S hT hS hmeet.
  case: (pselect (exists U, G U /\ T `&` U <> set0))=> [[U [hU hu]]|hn].
  * have [B [hB hb]] := @saturated_family_controls_intersections R X F d tau G hG
      T U hT hU hu.
    exists B; split=> //; by left.
  * have hrem C (hC : G C) : T `&` C = set0.
      case: (pselect (T `&` C = set0))=> [he|hne]; first exact he.
      exfalso; apply: hn; by exists C.
    have he : S = W.
      case: hS=> [hS|he]; last exact he.
      exfalso; apply: hn; by exists S.
    exists W; split; first by right.
    split; first by rewrite -he.
    exact: hlarge T hT hrem.
Qed.
