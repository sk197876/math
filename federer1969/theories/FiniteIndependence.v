(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: a finite family is linearly independent if every
    vanishing linear combination has zero coefficients. This predicate
    applies to arbitrary vector spaces, not just finite-dimensional ones. *)
Section Independence.
Variable K : fieldType.
Variable I : finType.
Variable V : lmodType K.
(** Source for [finite_independent]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition finite_independent (e : I -> V) :=
  forall c : I -> K, \sum_i c i *: e i = 0 -> forall i, c i = 0.
(** Source for [finite_independent_separating]: Federer (1969), 1.4.3, p.
    19, opening assertion and biorthogonal-vector argument. In words:
    Increasing products of a finite independent family of covectors are
    independent; evaluation on the corresponding products of biorthogonal
    vectors gives the Kronecker pairing. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_independent_separating (e : I -> V) (f : I -> {linear V -> K^o}) :
  (forall i j, f i (e j) = if i == j then 1 else 0) -> finite_independent e.
Proof.
move=> h c hc i; have he := congr1 (f i) hc.
rewrite linear_sum linear0 in he.
have hv : (\sum_j f i (c j *: e j)) = c i.
  under eq_bigr do rewrite linearZ h.
  change ((\sum_j c j * (if i == j then 1 else 0)) = c i).
  rewrite (bigD1 i) //= eqxx mulr1.
  have hz : (\sum_(j | j != i) c j * (if i == j then 1 else 0)) = 0.
    apply: big1 => j hj; by rewrite eq_sym (negbTE hj) mulr0.
  by rewrite hz addr0.
by rewrite hv in he.
Qed.
End Independence.

(** Source for [finite_independent_map]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_independent_map (K : fieldType) (I : finType) (V W : lmodType K)
    (f : {linear V -> W}) (e : I -> V) :
  injective f -> finite_independent e -> finite_independent (fun i => f (e i)).
Proof.
move=> hf he c hc; apply: he; apply: hf.
rewrite linear_sum linear0; under eq_bigr do rewrite linearZ.
exact: hc.
Qed.
