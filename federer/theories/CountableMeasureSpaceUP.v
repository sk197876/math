(** Federer (1969), 2.6.5, p. 119, finite products with arbitrary
    parenthesisations. This record packages an arbitrary factor with its
    proved laws; it does not postulate any measure or set-theoretic axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP CountablyMeasurableProduct ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_measure_space]: supporting package of the factors
    and their laws for corrected finite association in Federer 2.6.5, p. 119
    Carriers may be different or empty. *)
Record countable_measure_space (R : realType) : Type := {
  (** Source for [countable_measure_carrier]: the factor's
      underlying set, Federer 2.6.5, p. 119. *)
  countable_measure_carrier : choiceType;
  (** Source for [countable_measure_value]: its measure,
      Federer 2.6.5, p. 119. *)
  countable_measure_value : set countable_measure_carrier -> \bar R;
  (** Source for [countable_measure_law]: the proved measure
      laws for the factor, Federer 2.6.5, p. 119. *)
  countable_measure_law : is_measure countable_measure_value;
  (** Source for [countable_measure_cover_law]: Supporting Federer 2.6.5, p.
    119. *)
  countable_measure_cover_law : measure_countably_measurable countable_measure_value setT
}.
Arguments countable_measure_carrier {R} c.
Arguments countable_measure_value {R} c _.
Arguments countable_measure_law {R} c.
Arguments countable_measure_cover_law {R} c.

(** Source for [countable_measure_product]: supporting closure of the
    corrected factors under binary products, Federer 2.6.5, p. 119 The
    measure itself is the existing sealed binary product; its laws are
    proved. *)
Definition countable_measure_product (R : realType) (A B : countable_measure_space R) : countable_measure_space R :=
  @Build_countable_measure_space R
    [the choiceType of (countable_measure_carrier A * countable_measure_carrier B)%type]
    (product_measure (countable_measure_law A) (countable_measure_law B))
    (product_measure_is_measure (countable_measure_law A) (countable_measure_law B))
    (@product_whole_countably_measurable R (countable_measure_carrier A) (countable_measure_carrier B)
      (countable_measure_value A) (countable_measure_value B)
      (countable_measure_law A) (countable_measure_law B)
      (countable_measure_cover_law A) (countable_measure_cover_law B)).
