(** Domain-precise enlargement notation for Federer (1969), 2.8.7, p. 144,
    using the definition immediately before 2.8.5 on that page. Delta is
    defined on F itself. Total extensions serve only as witnesses for
    applying the auxiliary interface; their laws determine all relevant
    enlargement sets. No chosen extension is exported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import WeightedEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_family_weight_extension]: supporting
    representation law for the function on F in Federer
    2.8.7, p. 144. The total function agrees with delta
    at every eligible set; its other values are irrelevant.
    This predicate asserts laws, not an unproved axiom. *)
Definition is_family_weight_extension (R : realType) (X : choiceType)
    (F : set (set X)) (delta : {T : set X | F T} -> R) (d : set X -> R) :=
  forall T (hT : F T), d T = delta (exist F T hT).

(** Source for [family_weighted_enlargement]: the enlargement in Federer
    2.8.7, p. 144, defined immediately before 2.8.5 Both delta and the
    eligible member S have their exact printed domains. *)
Definition family_weighted_enlargement (R : realType) (X : choiceType)
    (F : set (set X)) (delta : {T : set X | F T} -> R)
    (tau : R) (S : {S : set X | F S}) :=
  \bigcup_(T in [set T : {T : set X | F T} |
    sval T `&` sval S <> set0 /\ delta T <= tau * delta S]) sval T.

(** Source for [family_weighted_enlargement_extension]: supporting
    invariance of the enlargement used in Federer 2.8.7, p. 144, under total
    extension of the weight. It follows from the defining membership
    formula. *)
Lemma family_weighted_enlargement_extension (R : realType) (X : choiceType)
    (F : set (set X)) (delta : {T : set X | F T} -> R)
    (d : set X -> R) (tau : R) :
  is_family_weight_extension delta d -> forall S,
  weighted_enlargement F d tau (sval S) = family_weighted_enlargement delta tau S.
Proof.
move=> hd [S hS]; apply/seteqP; split.
- move=> x [T [hT [hmeet hbound]] hx].
  exists (exist F T hT); last exact hx.
  split=> //; by move: hbound; rewrite (hd T hT) (hd S hS).
- move=> x [[T hT] [hmeet hbound] hx].
  exists T; last exact hx.
  split=> //; split=> //; by rewrite (hd T hT) (hd S hS).
Qed.

(** Source for [family_weight_extension_exists]: supporting
    existence of a total representative of the function on F
    in Federer 2.8.7, p. 144. Zero is assigned outside
    F only inside this opaque existence proof. Subsequent
    proofs use the extension laws and never this construction. *)
Theorem family_weight_extension_exists (R : realType) (X : choiceType)
    (F : set (set X)) (delta : {T : set X | F T} -> R) :
  exists d, is_family_weight_extension delta d.
Proof.
pose d T := match pselect (F T) with
  | left h => delta (exist F T h)
  | right _ => 0
  end.
exists d=> T hT; rewrite /d.
case: (pselect (F T))=> [h|h]; last by contradiction.
have he : exist F T h = exist F T hT by apply: eq_exist.
by rewrite he.
Qed.
