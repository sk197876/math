(** Public selection interface for Federer (1969), 2.8.4, p. 143. The
    weights may vanish; eligible sets must be nonempty, as corrected by the
    erratum p. 3 (book p. 143 line 17). The proof uses only the sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import CountablyClosedFamilyUP WeightedCoverSelectionUP
  WeightedCoverSelectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_cover_selection]: the G in Federer
    2.8.4, p. 143. For this auxiliary interface the
    weight is total on sets; only its restriction to F is used.
    The public book theorem below takes the weight on F itself. *)
Definition weighted_cover_selection (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (he : forall T, F T -> T <> set0)
    (hn : forall T, F T -> 0 <= d T)
    (hb : exists C, forall T, F T -> d T <= C) (ht : 1 < tau) :=
  @WeightedCoverSelection.value R X F d tau he hn hb ht.

(** Source for [weighted_cover_selection_specification]:
    the membership, disjointness, intersection and weight
    comparison laws of Federer 2.8.4, p. 143. *)
Theorem weighted_cover_selection_specification (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (he : forall T, F T -> T <> set0)
    (hn : forall T, F T -> 0 <= d T)
    (hb : exists C, forall T, F T -> d T <= C) (ht : 1 < tau) :
  is_weighted_cover_selection F d tau
    (@weighted_cover_selection R X F d tau he hn hb ht).
Proof. exact: WeightedCoverSelection.laws. Qed.

(** Source for [federer_2_8_4]: direct formalisation of the corrected
    theorem in Federer 2.8.4, p. 143, with delta defined on F itself and
    with empty members excluded (erratum p. 3, book p. 143 line 17). The
    conclusion is purely set theoretic, so the unused metric, closedness and
    measure hypotheses of 2.8.1 are omitted, as observed. No positivity of
    delta is added and the selected family need not be countable. *)
Theorem federer_2_8_4 (R : realType) (X : choiceType)
    (F : set (set X)) (delta : {T : set X | F T} -> R) (tau : R) :
  (forall T, F T -> T <> set0) -> (forall T, 0 <= delta T) ->
  (exists C, forall T, delta T <= C) -> 1 < tau ->
  exists (G : set (set X)) (hGF : G `<=` F),
    set_family_disjoint G /\ forall T (hT : F T),
    exists (S : set X) (hS : G S), T `&` S <> set0 /\
      delta (exist F T hT) <= tau * delta (exist F S (hGF S hS)).
Proof.
move=> he hn hb ht.
pose d T := match pselect (F T) with
  | left h => delta (exist F T h)
  | right _ => 0
  end.
have hd T (hT : F T) : d T = delta (exist F T hT).
  rewrite /d; case: (pselect (F T))=> [h|h]; last by contradiction.
  have hp : exist F T h = exist F T hT by apply: eq_exist.
  by rewrite hp.
have hnon T (hT : F T) : 0 <= d T by rewrite (hd T hT); exact: hn.
have hbound : exists C, forall T, F T -> d T <= C.
  have [C hC] := hb; exists C=> T hT; rewrite (hd T hT); exact: hC.
pose G := @weighted_cover_selection R X F d tau he hnon hbound ht.
have hG : is_weighted_cover_selection F d tau G.
  exact: weighted_cover_selection_specification.
pose hGF := @weighted_selection_members R X F d tau G hG.
exists G, hGF; split; first exact: weighted_selection_disjoint hG.
move=> T hT.
have [S [hS [hmeet hweight]]] := @weighted_selection_dominates R X F d tau G hG T hT.
exists S, hS; split=> //.
by move: hweight; rewrite (hd T hT) (hd S (hGF S hS)).
Qed.
