(** General topology supporting the complete separable source in Federer
    (1969), 2.10.5, p. 172, using 2.2.10, p. 65. From a countable open base
    choose a point in each nonempty member; the resulting countable range is
    dense. A supplied ambient point handles empty basic members, rather than
    assuming that every base element is nonempty. Source context and base
    convention: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_open_base_dense_set]: supporting
    separability from a countable open base for the
    Euclidean and projection spaces in Federer 2.10.5,
    p. 172. The conclusion gives the dense set
    existentially; no point enumeration is exposed. *)
Theorem countable_open_base_dense_set (X : topologicalType) (a : X)
    (U : nat -> set X) : is_countable_open_base U ->
  exists D : set X, countable D /\ dense D.
Proof.
move=> hU.
have hex n : exists x : X, (exists y, U n y) -> U n x.
  case: (pselect (exists y, U n y))=> [[y hy]|hn].
  - by exists y.
  - by exists a=> h; exfalso; exact: hn h.
pose e n := projT1 (cid (hex n)).
have he n := projT2 (cid (hex n)).
exists (e @` setT); split.
- exact: sub_countable (card_image_le e setT) (countableP setT).
- move=> W [x hx] ho.
  have [n [hn hsub]] := @countable_base_refines X U hU W ho x hx.
  have hne : exists y, U n y by exists x.
  exists (e n); split; first exact: hsub _ (he n hne).
  by exists n.
Qed.
