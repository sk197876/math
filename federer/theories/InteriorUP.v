(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import ExteriorHomogeneousProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1, opening paragraph: the characteristic conditions
    define the two operations independently of their constructions. *)
Section CharacteristicConditions.
Variable K : fieldType.
Variables V W : lmodType K.
Variables p q : nat.
(** Source for [is_right_interior]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition is_right_interior
  (i : exterior_power V p -> A_m V W q -> A_m V W (q-p)) : Prop :=
  bilinear i /\ forall eta phi xi,
    pairing xi (i eta phi) =
      form_homogeneous phi (wedge (component_val xi) (component_val eta)).
Hypothesis h2 : (1+1 : K) != 0.
Variable hpq : (p <= q)%N.
(** Source for [is_left_interior]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition is_left_interior
  (i : exterior_power V q -> A_m V K^o p -> exterior_power V (q-p)) : Prop :=
  bilinear i /\ forall zeta a b,
    pairing (i zeta a) b =
      pairing zeta (form_reindex (subnKC hpq) (form_wedge h2 (scalar_bilinear K) a b)).
End CharacteristicConditions.
