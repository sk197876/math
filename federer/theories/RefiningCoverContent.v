(** Federer (1969), 2.10.47, p. 204: gamma_i is the infimum of zeta-costs
    over countable covers drawn from the cube families H_j with j>=i. This
    file specifies that infimum for an abstract family H before exposing a
    witness through the existing opaque covering envelope. The Euclidean
    cube construction and comparisons with Hausdorff cutoffs are separate
    obligations. No construction module is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import CountableCoverEnvelopeUP CountableCoverEnvelopeBasic CountableCoverEnvelopeLaws
  CountableCoverEnvelopeSealed MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [refining_cover_tail]: the union of H_j
    over j>=i in the definition of gamma_i in
    2.10.47, p. 204. Sets, not occurrences, index covers. *)
Definition refining_cover_tail (X : choiceType) (H : nat -> set (set X)) i : set (set X) :=
  [set S | exists j, (i<=j)%N /\ H j S].

(** Source for [is_refining_cover_content]: abstract infimum
    law defining gamma_i in 2.10.47, p. 204. *)
Definition is_refining_cover_content (R : realType) (X : choiceType)
    (H : nat -> set (set X)) (cost : set X -> \bar R) i (gamma : set X -> \bar R) :=
  is_countable_cover_envelope (fun S : set_type (refining_cover_tail H i)=>val S)
    (fun S=>cost (val S)) gamma.

(** Source for [refining_cover_content_measure]: the printed
    assertion that gamma_i are measures in 2.10.47,
    p. 204, from 2.10.1's covering argument. *)
Lemma refining_cover_content_measure (R : realType) (X : choiceType) H cost i gamma :
  @is_refining_cover_content R X H cost i gamma ->
  (forall S, refining_cover_tail H i S -> 0<=cost S) -> is_measure gamma.
Proof.
move=> hg hc; apply: (countable_cover_envelope_is_measure hg)=> S.
exact: hc _ (set_valP S).
Qed.

(** Source for [refining_cover_content_generator]: gamma_i(S)
    is at most zeta(S) for an eligible cube, used in
    2.10.47, p. 205, immediately before the last invariant. *)
Lemma refining_cover_content_generator (R : realType) (X : choiceType) H cost i gamma S :
  @is_refining_cover_content R X H cost i gamma ->
  refining_cover_tail H i S -> 0<=cost S -> gamma S<=cost S.
Proof.
move=> hg hS hc.
pose s : set_type (refining_cover_tail H i) := exist _ S (mem_set hS).
exact (@countable_cover_envelope_generator_bound R X _ _ _ gamma hg s hc).
Qed.

(** Source for [refining_cover_content_comparison]: supporting
    covering comparison for gamma_i in 2.10.47, p. 204.
    A measure bounded by every eligible generator's cost is
    bounded by the content on every set. *)
Lemma refining_cover_content_comparison (R : realType) (X : choiceType) H cost i gamma
    (mu : set X -> \bar R) :
  @is_refining_cover_content R X H cost i gamma -> is_measure mu ->
  (forall S, refining_cover_tail H i S -> mu S<=cost S) -> forall A, mu A<=gamma A.
Proof.
move=> hg hm hbound A; apply: (countable_cover_envelope_greatest hg)=> G hG hcov.
apply: le_trans (measure_indexed_cover hm hG hcov) _.
apply: nonnegative_sum_mono=> S hS; exact: hbound _ (set_valP S).
Qed.

(** Source for [refining_cover_content_nondecreasing]: gamma_i
    increases with i, used to choose D_S in 2.10.47,
    p. 205. Restricting the available levels increases
    the covering infimum. *)
Lemma refining_cover_content_nondecreasing (R : realType) (X : choiceType) H cost i j gamma eta :
  @is_refining_cover_content R X H cost i gamma ->
  is_refining_cover_content H cost j eta ->
  (forall S, refining_cover_tail H i S -> 0<=cost S) ->
  (i<=j)%N -> forall A, gamma A<=eta A.
Proof.
move=> hg he hc hij.
apply: (refining_cover_content_comparison he (refining_cover_content_measure hg hc))=> S [k [hjk hSk]].
have hS : refining_cover_tail H i S by exists k; split=> //; exact: leq_trans hij hjk.
exact: refining_cover_content_generator hg hS (hc S hS).
Qed.

(** Source for [refining_cover_content]: opaque witness for
    the infimum gamma_i of 2.10.47, p. 204. The
    fixed-family existence proof is already sealed; this
    public adapter does not inspect its implementation. *)
Definition refining_cover_content (R : realType) (X : choiceType)
    (H : nat -> set (set X)) (cost : set X -> \bar R) i :=
  @CountableCoverEnvelope.value R X (set_type (refining_cover_tail H i))
    (fun S=>val S) (fun S=>cost (val S)).

(** Source for [refining_cover_content_specification]: proved
    defining laws of gamma_i in 2.10.47, p. 204. *)
Lemma refining_cover_content_specification (R : realType) (X : choiceType)
    (H : nat -> set (set X)) (cost : set X -> \bar R) i :
  is_refining_cover_content H cost i (@refining_cover_content R X H cost i).
Proof. exact: CountableCoverEnvelope.laws. Qed.
