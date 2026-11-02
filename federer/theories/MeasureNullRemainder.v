(** Federer (1969), 2.6.2, p. 117: deleting a null remainder from a
    measurable enclosing section preserves measurability and its measure.
    This supporting set lemma uses completeness and the splitting law from
    2.1.3, p. 55; no finiteness assumption is needed after the remainder is
    null. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_subset_null_remainder]: supporting section
    conclusion in Federer 2.6.2, p. 117 If A is contained in measurable B
    and B minus A is null, then A is measurable and has B's measure, even
    when it is infinite. *)
Lemma measurable_subset_null_remainder (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  A `<=` B -> measure_measurable mu B -> mu (B `\` A) = 0 ->
  measure_measurable mu A /\ mu A = mu B.
Proof.
move=> hab hb hz.
have he : A = B `\` (B `\` A).
  apply/seteqP; split.
  - move=> x hx; split; first exact: hab x hx.
    by move=> [_ hn]; exact: hn hx.
  - move=> x [hx hn]; apply: contrapT=> ha; apply: hn; by split.
have ha : measure_measurable mu A.
  rewrite he; exact (@measure_measurable_difference R X mu hm B (B `\` A) hb (measure_null_measurable hm hz)).
split=> //.
have hi : B `&` A = A.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hab x hx.
have h := ha B; by rewrite hi hz adde0 in h.
Qed.
