(** Federer (1969), 2.6.2, p. 116: each member of P1 is a union of a
    countable disjoint family of measurable rectangles. We first specify the
    family by its measurable factors, disjointness, and union; existence is
    proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_disjoint_rectangle_cover]: abstract
    specification of the disjoint family of measurable rectangles
    used in Federer 2.6.2, p. 116. Cardinality is
    kept separate so the same laws apply to finite and countable families. *)
Record is_disjoint_rectangle_cover (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (G : set (set X * set Y)) (S : set (X * Y)) : Prop := {
  (** Source for [disjoint_rectangle_factors]: the factors of
      each member of P0 are measurable in Federer 2.6.2, p. 116. *)
  disjoint_rectangle_factors : forall p, G p ->
    measure_measurable alpha p.1 /\ measure_measurable beta p.2;
  (** Source for [disjoint_rectangle_pieces]: the disjointness
      in the P1 representation of Federer 2.6.2, p. 116. *)
  disjoint_rectangle_pieces : forall p q, G p -> G q -> p <> q ->
    forall z, (p.1 `*` p.2) z -> (q.1 `*` q.2) z -> False;
  (** Source for [disjoint_rectangle_union]: the covering
      equality in the P1 representation of Federer 2.6.2, p. 116. *)
  disjoint_rectangle_union : S = \bigcup_(p in G) (p.1 `*` p.2)
}.

(** Source for [finite_disjoint_rectangle_union]: the family of finite
    disjoint unions implicit in Federer 2.6.2, p. 116 This is an existence
    predicate, not a chosen construction. *)
Definition finite_disjoint_rectangle_union (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (S : set (X * Y)) :=
  exists G, finite_set G /\ is_disjoint_rectangle_cover alpha beta G S.

(** Source for [disjoint_rectangle_cover_subset]: supporting
    fact that each member of the disjoint family lies in
    its union in Federer 2.6.2, p. 116. *)
Lemma disjoint_rectangle_cover_subset (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (G : set (set X * set Y)) (S : set (X * Y)) :
  is_disjoint_rectangle_cover alpha beta G S -> forall p, G p -> p.1 `*` p.2 `<=` S.
Proof. move=> h p hp z hz; rewrite (disjoint_rectangle_union h); by exists p. Qed.
