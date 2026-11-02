(** Federer (1969), 2.8.5, p. 144, including the unnumbered definition of
    delta,tau enlargement immediately before the corollary. This is a set
    operation given by its printed membership formula; selection witnesses
    are used only through their abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import WeightedCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_enlargement]: the formula for the delta,tau
    enlargement preceding Federer 2.8.5, p. 144 It is the union of eligible
    T that meet S and satisfy delta(T)<=tau delta(S). Only values of the
    auxiliary total weight on F are used when S belongs to F. *)
Definition weighted_enlargement (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) (S : set X) :=
  \bigcup_(T in [set T | F T /\ T `&` S <> set0 /\ d T <= tau * d S]) T.

(** Source for [weighted_enlargement_contains_member]: the inclusion T
    subset hat(S) from the defining formula preceding Federer 2.8.5, p. 144
    No topology or measure is needed. *)
Lemma weighted_enlargement_contains_member (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) (T S : set X) :
  F T -> T `&` S <> set0 -> d T <= tau * d S ->
  T `<=` weighted_enlargement F d tau S.
Proof.
move=> hT hmeet hweight x hx; exists T=> //; by split=> //; split.
Qed.

(** Source for [weighted_enlargement_contains_self]: Supporting Federer
    2.8.5, p. 144.Empty S is included vacuously; no positive-weight
    hypothesis is imposed. *)
Lemma weighted_enlargement_contains_self (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) (S : set X) :
  F S -> 0 <= d S -> 1 <= tau -> S `<=` weighted_enlargement F d tau S.
Proof.
move=> hS hd ht x hx.
have hnonempty : S `&` S <> set0.
  move=> he; have hs : (S `&` S) x by split.
  by rewrite he in hs.
have hweight : d S <= tau * d S.
  have h := ler_wpM2r hd ht; by rewrite mul1r in h.
exact (@weighted_enlargement_contains_member R X F d tau S S hS hnonempty hweight x hx).
Qed.

(** Source for [weighted_enlargement_mono_family]: supporting restriction of
    an enlargement to a subfamily in later applications of Federer 2.8.5, p.
    144. Enlarging the eligible family with fixed weights and factor only
    enlarges the union. *)
Lemma weighted_enlargement_mono_family (R : realType) (X : choiceType)
    (F H : set (set X)) (d : set X -> R) (tau : R) (S : set X) :
  F `<=` H -> weighted_enlargement F d tau S `<=` weighted_enlargement H d tau S.
Proof.
move=> hFH x [T [hT [hmeet hweight]] hx].
exists T=> //; split; first exact: hFH T hT.
by split.
Qed.

(** Source for [weighted_selection_enlargement_cover]: direct formalisation
    of Federer 2.8.5, p. 144 The selected enlargements cover union F. The
    premise is the abstract conclusion of 2.8.4, so no chosen maximal-family
    construction is unfolded. *)
Theorem weighted_selection_enlargement_cover (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R) (G : set (set X)) :
  is_weighted_cover_selection F d tau G ->
  (\bigcup_(T in F) T) `<=` \bigcup_(S in G) weighted_enlargement F d tau S.
Proof.
move=> hG x [T hT hx].
have [S [hS [hmeet hweight]]] := @weighted_selection_dominates R X F d tau G hG T hT.
exists S=> //.
exact (@weighted_enlargement_contains_member R X F d tau T S hT hmeet hweight x hx).
Qed.
