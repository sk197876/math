(** Federer (1969), 2.6.5, p. 119: finite products with arbitrary
    associations. We make the finite parenthesisations explicit and keep the
    ordered factor values visible, so the final identification is the
    canonical coordinate identification, not just an unspecified isomorphism
    of measures. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import CountableMeasureSpaceUP MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_product_tree]: supporting syntax for all nonempty
    finite parenthesisations in Federer 2.6.5, p. 119 *)
Inductive measure_product_tree (R : realType) : Type :=
  (** Source for [MeasureFactor]: one original measure in
      the finite product of Federer 2.6.5, p. 119. *)
  | MeasureFactor : countable_measure_space R -> measure_product_tree R
  (** Source for [MeasurePair]: a binary grouping in the
      finite product of Federer 2.6.5, p. 119. *)
  | MeasurePair : measure_product_tree R -> measure_product_tree R -> measure_product_tree R.
Arguments MeasureFactor {R} A.
Arguments MeasurePair {R} t u.

(** Source for [measure_tree_space]: the actual iterated
    measure and carrier associated with a parenthesisation
    in Federer 2.6.5, p. 119. Binary measures are
    supplied by the sealed product interface. *)
Fixpoint measure_tree_space (R : realType) (t : measure_product_tree R) : countable_measure_space R :=
  match t with
  | MeasureFactor A => A
  | MeasurePair u v => countable_measure_product (measure_tree_space u) (measure_tree_space v)
  end.

(** Source for [measure_tree_factors]: supporting ordered
    list of factors whose associations are compared in
    Federer 2.6.5, p. 119. *)
Fixpoint measure_tree_factors (R : realType) (t : measure_product_tree R) : seq (countable_measure_space R) :=
  match t with
  | MeasureFactor A => [:: A]
  | MeasurePair u v => measure_tree_factors u ++ measure_tree_factors v
  end.

(** Source for [labelled_measure_point]: supporting value
    of one labelled factor in Federer 2.6.5, p. 119.
    The dependent pair keeps the carrier with its value,
    even when different factors have different underlying sets. *)
Definition labelled_measure_point (R : realType) :=
  {A : countable_measure_space R & countable_measure_carrier A}.

(** Source for [measure_tree_coordinates]: supporting
    ordered coordinate values in the canonical finite-product
    identifications of Federer 2.6.5, p. 119. *)
Fixpoint measure_tree_coordinates (R : realType) (t : measure_product_tree R) :
    countable_measure_carrier (measure_tree_space t) -> seq (labelled_measure_point R) :=
  match t as u return countable_measure_carrier (measure_tree_space u) -> seq (labelled_measure_point R) with
  | MeasureFactor A => fun x => [:: existT _ A x]
  | MeasurePair u v => fun p => @measure_tree_coordinates R u p.1 ++ @measure_tree_coordinates R v p.2
  end.
Arguments measure_tree_coordinates {R} t x.

(** Source for [is_measure_tree_identification]: abstract
    laws for canonical identification of two associations
    in Federer 2.6.5, p. 119: it is a measure-preserving
    bijection retaining every ordered factor coordinate. *)
Record is_measure_tree_identification (R : realType) (t u : measure_product_tree R)
    (f : countable_measure_carrier (measure_tree_space t) -> countable_measure_carrier (measure_tree_space u))
    (g : countable_measure_carrier (measure_tree_space u) -> countable_measure_carrier (measure_tree_space t)) : Prop := {
  (** Source for [measure_tree_identification_measure]:
      image-measure law under the coordinate identification,
      Federer 2.6.5, p. 119. *)
  measure_tree_identification_measure : is_measure_bijection
    (countable_measure_value (measure_tree_space t)) (countable_measure_value (measure_tree_space u)) f g;
  (** Source for [measure_tree_identification_coordinates]:
      the canonical map preserves the ordered coordinates,
      as in the displayed s of Federer 2.6.5, p. 119. *)
  measure_tree_identification_coordinates : forall x, measure_tree_coordinates u (f x) = measure_tree_coordinates t x
}.
Arguments is_measure_tree_identification {R} t u f g.
