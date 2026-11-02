(** Federer (1969), Theorem 2.8.4, p. 143, corrected by the erratum p. 3
    (book p. 143 line 17): empty members must be excluded. The laws below
    are purely set theoretic; topology and measure play no part in them. The
    auxiliary weight is total, but only values on F are used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_weighted_cover_selection]: the disjointed subfamily G and
    its intersection and weight comparison properties in Federer 2.8.4, p.
    143 This specifies the selection independently of the existence proof. *)
Record is_weighted_cover_selection (R : realType) (X : choiceType)
    (F : set (set X)) (delta : set X -> R) (tau : R)
    (G : set (set X)) : Prop := {
  (** Source for [weighted_selection_members]: G is a
      subfamily of F, Federer 2.8.4, p. 143. *)
  weighted_selection_members : G `<=` F;
  (** Source for [weighted_selection_disjoint]: G is
      disjointed, Federer 2.8.4, p. 143. *)
  weighted_selection_disjoint : set_family_disjoint G;
  (** Source for [weighted_selection_dominates]: each T in
      F meets some S in G with delta(T)<=tau delta(S),
      Federer 2.8.4, p. 143. *)
  weighted_selection_dominates : forall T, F T -> exists S,
    G S /\ T `&` S <> set0 /\ delta T <= tau * delta S
}.

(** Source for [is_weight_saturated_family]: the class Q used in the proof
    of Federer 2.8.4, p. 143 Every eligible T meeting the family has a
    sufficiently large intersecting member. Maximality is a separate
    condition. *)
Record is_weight_saturated_family (R : realType) (X : choiceType)
    (F : set (set X)) (delta : set X -> R) (tau : R)
    (G : set (set X)) : Prop := {
  (** Source for [saturated_family_members]: membership in
      F for the auxiliary class Q, Federer 2.8.4, p. 143. *)
  saturated_family_members : G `<=` F;
  (** Source for [saturated_family_disjoint]: disjointness in
      the auxiliary class Q, Federer 2.8.4, p. 143. *)
  saturated_family_disjoint : set_family_disjoint G;
  (** Source for [saturated_family_controls_intersections]: the alternative
    defining Q in Federer 2.8.4, p. 143, phrased as an implication from an
    intersecting member *)
  saturated_family_controls_intersections : forall T S,
    F T -> G S -> T `&` S <> set0 -> exists U,
      G U /\ T `&` U <> set0 /\ delta T <= tau * delta U
}.
