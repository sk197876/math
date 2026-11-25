(** Federer (1969), 2.5.10, p. 101, final paragraph: a maximal disjoint
    family of compact sets with the stated positive-neighborhood property.
    We separate the general maximal-family law from the particular
    compact-set predicate. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_maximal_disjoint_family]: abstract maximal-family
    specification supporting Federer 2.5.10, p. 101 P describes the eligible
    sets. *)
Record is_maximal_disjoint_family (X : choiceType) (P G : set (set X)) : Prop := {
  (** Source for [maximal_disjoint_family_members]: eligibility
      of the compact pieces in Federer 2.5.10, p. 101. *)
  maximal_disjoint_family_members : G `<=` P;
  (** Source for [maximal_disjoint_family_disjoint]: disjointness
      of the chosen family in Federer 2.5.10, p. 101. *)
  maximal_disjoint_family_disjoint : set_family_disjoint G;
  (** Source for [maximal_disjoint_family_maximal]: inclusion maximality in
    Federer 2.5.10, p. 101 *)
  maximal_disjoint_family_maximal : forall F, F `<=` P -> set_family_disjoint F -> G `<=` F -> F `<=` G
}.
