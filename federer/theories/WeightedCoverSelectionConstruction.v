(** Private maximal-family construction for Federer (1969), Theorem 2.8.4,
    p. 143 General set-theoretic Zorn is used as the background maximal
    principle, as elsewhere in this project. No external covering theorem is
    imported. The corrected exclusion of empty members is essential in the
    final contradiction. Source context and erratum:
    WeightedCoverSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import CountablyClosedFamilyUP WeightedCoverSelectionUP
  WeightedSaturationLaws LargeWeightedMember.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [maximal_weight_saturated_family_exists]: the maximal G in Q
    in Federer 2.8.4, p. 143 This private existence lemma does not assume
    bounded or positive weights; those are used only later. *)
Theorem maximal_weight_saturated_family_exists (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) :
  exists G, is_weight_saturated_family F d tau G /\
    forall H, is_weight_saturated_family F d tau H -> G `<=` H -> H `<=` G.
Proof.
pose Q G := is_weight_saturated_family F d tau G.
pose T := {G : set (set X) | Q G}.
pose rel (a b : T) := `[< sval a `<=` sval b >].
have hrefl a : rel a a by apply/asboolP.
have htrans a b c : rel a b -> rel b c -> rel a c.
  move=> /asboolP hab /asboolP hbc; apply/asboolP=> S hS; exact: hbc (hab S hS).
have hanti a b : rel a b -> rel b a -> a = b.
  move=> /asboolP hab /asboolP hba; case: a hab hba=> a ha; case: b=> b hb hab hba.
  apply: eq_exist; apply/seteqP; by split.
have hchain (C : set T) : total_on C rel -> exists b, forall a, C a -> rel a b.
  move=> hc.
  pose D := sval @` C.
  have hs H : D H -> is_weight_saturated_family F d tau H.
    by move=> [a ha <-]; exact: svalP a.
  have hcomp H K : D H -> D K -> H `<=` K \/ K `<=` H.
    move=> [a ha <-] [b hb <-].
    have [/asboolP hab|/asboolP hba] := hc a b ha hb; by [left|right].
  pose U := \bigcup_(H in D) H.
  have hU : Q U := @chain_union_weight_saturated R X F d tau D hs hcomp.
  exists (exist Q U hU)=> a ha; apply/asboolP=> S hS.
  exists (sval a); last exact hS.
  by exists a.
have [a hmax] := @Zorn T rel hrefl htrans hanti hchain.
exists (sval a); split; first exact: svalP a.
move=> H hH hGH; pose b : T := exist Q H hH.
have hab : rel a b by apply/asboolP.
have he := hmax b hab; change (sval b `<=` sval a); by rewrite he.
Qed.

(** Source for [weighted_cover_selection_exists]: the full conclusion of
    Federer 2.8.4, p. 143, with the erratum p. 3 (book p. 143 line 17)
    excluding empty members A maximal saturated family leaves no eligible
    set disjoint from it, since a sufficiently large such set could be
    adjoined. *)
Theorem weighted_cover_selection_exists (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) :
  (forall T, F T -> T <> set0) ->
  (forall T, F T -> 0 <= d T) ->
  (exists C, forall T, F T -> d T <= C) -> 1 < tau ->
  exists G, is_weighted_cover_selection F d tau G.
Proof.
move=> hnonempty hnon hbound ht.
have [G [hG hmax]] := @maximal_weight_saturated_family_exists R X F d tau.
exists G; constructor.
- exact: saturated_family_members hG.
- exact: saturated_family_disjoint hG.
- move=> T hT.
  case: (pselect (exists S, G S /\ T `&` S <> set0))=> [[S [hS hs]]|hn].
  * exact (@saturated_family_controls_intersections R X F d tau G hG T S hT hS hs).
  * pose K := [set B : set X | F B /\ forall S, G S -> B `&` S = set0].
    have hTK : K T.
      split=> // S hS; case: (pselect (T `&` S = set0))=> [he|hne]; first exact he.
      exfalso; apply: hn; by exists S.
    have hKnon B (hB : K B) : 0 <= d B := hnon B hB.1.
    have hKb : exists C, forall B, K B -> d B <= C.
      have [C hC] := hbound; exists C=> B hB; exact: hC B hB.1.
    have [W [hW hlarge]] := @bounded_nonnegative_large_member R [the choiceType of set X]
      K d tau (ex_intro _ T hTK) hKnon hKb ht.
    have hi : is_weight_saturated_family F d tau (G `|` [set W]).
      apply: (@saturated_family_insert_large_remaining R X F d tau G W hG hW.1 hW.2).
      move=> B hB hdis; exact: hlarge B (conj hB hdis).
    have hsub : G `<=` G `|` [set W] by move=> B hB; left.
    have hWG : G W := hmax _ hi hsub W (or_intror (erefl _)).
    have he := hW.2 W hWG; rewrite setIid in he.
    exfalso; exact: hnonempty W hW.1 he.
Qed.
