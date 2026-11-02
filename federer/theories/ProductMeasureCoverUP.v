(** Federer (1969), 2.6.1, pp. 114–115: infimum of the sums of rectangle
    costs over countable covers by measurable rectangles. We initially use
    countable families of pairs of measurable sets; the sequence formulation
    is verified separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_product_cover_infimum]: the defining infimum in Federer
    2.6.1, pp. 114–115 The lower-bound and greatest-lower-bound laws avoid
    choosing particular covers or approximation sequences. *)
Record is_product_cover_infimum (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (nu : set (X * Y) -> \bar R) : Prop := {
  (** Source for [product_cover_lower]: each admissible rectangle
      covering cost bounds the infimum in Federer 2.6.1, pp. 114–115. *)
  product_cover_lower : forall S (G : set (set X * set Y)), countable G ->
    (forall p, G p -> measure_measurable alpha p.1 /\ measure_measurable beta p.2) ->
    S `<=` (\bigcup_(p in G) (p.1 `*` p.2)) ->
    nu S <= nonnegative_sum G (fun p => alpha p.1 * beta p.2);
  (** Source for [product_cover_greatest]: greatest-lower-bound
      clause of the infimum in Federer 2.6.1, pp. 114–115. *)
  product_cover_greatest : forall S c,
    (forall G : set (set X * set Y), countable G ->
      (forall p, G p -> measure_measurable alpha p.1 /\ measure_measurable beta p.2) ->
      S `<=` (\bigcup_(p in G) (p.1 `*` p.2)) ->
      c <= nonnegative_sum G (fun p => alpha p.1 * beta p.2)) -> c <= nu S
}.
