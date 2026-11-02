(** Federer (1969), 2.1.6, p. 58: Ulam numbers. Cardinalities are
    represented by sets and injection comparison; the defining property is
    invariant under equipollence. The measure is defined on an ambient type
    and tested on a subset X, permitting empty carriers without a
    distinguished point. This is the relative version of Federer's
    definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [is_ulam_set]: Federer 2.1.6, p. 58, first
    definition, paraphrased: every finite measure on a set of at most
    the specified cardinality, with all subsets measurable and all
    singletons null, has zero total measure. The set D represents
    the cardinal bound; the property introduces no project axiom. *)
Definition is_ulam_set (R : realType) (J : choiceType) (D : set J) :=
  forall (I : choiceType) (mu : set I -> \bar R) (X : set I),
    is_measure mu -> X #<= D -> mu X < +oo ->
    (forall A, A `<=` X -> measure_measurable mu A) ->
    (forall x, X x -> mu [set x] = 0) -> mu X = 0.

(** Source for [ulam_set_downward]: Federer 2.1.6, p. 58,
    the Ulam cardinals form an initial segment. This is downward
    closure under injection comparison of cardinal representatives. *)
Lemma ulam_set_downward (R : realType) (I J : choiceType)
    (A : set I) (B : set J) : A #<= B -> is_ulam_set R B -> is_ulam_set R A.
Proof.
move=> hAB hB K mu X hm hX hf ha hz.
apply: (hB K mu X hm _ hf ha hz).
exact: card_le_trans hX hAB.
Qed.

(** Source for [ulam_set_cardinal_invariant]: Federer 2.1.6,
    p. 58, supporting well-definedness as a property of cardinal
    numbers: equipollent representatives have the same Ulam property. *)
Lemma ulam_set_cardinal_invariant (R : realType) (I J : choiceType)
    (A : set I) (B : set J) : A #= B -> (is_ulam_set R A <-> is_ulam_set R B).
Proof.
move=> /card_eqPle [hAB hBA]; split.
- exact: ulam_set_downward hBA.
- exact: ulam_set_downward hAB.
Qed.
