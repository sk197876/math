(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP GradedAlgebra
  FamilyUpdate TensorFamilyUP WordEvaluation PowerWords TensorAlgebraUP
  TensorAlgebra TensorGrading TensorPowers AlgebraQuotient ExteriorIdeal
  ExteriorAlgebraUP ExteriorQuotient ExteriorQuotientGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Existence of an exterior algebra (Federer 1.3.1): the quotient of the
    tensor algebra by mV satisfies [is_exterior_power_algebra]. The
    construction is used only through [exterior_quotient_exists]. *)
Section Witness.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation pi := (quotient_projection (mV V)).

(** Source for [exterior_quotient_generator]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Definition
    or construction used to formalise this passage. *)
Definition exterior_quotient_generator : {linear V -> exterior_algebra V} :=
  GRing.Linear.clone _ _ _ _ (@exterior_generator K V) _.

(** Source for [word_eval_exterior_generator]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma word_eval_exterior_generator s :
  word_eval exterior_quotient_generator s = exterior_word s.
Proof.
elim: s => [|v s ih] //=.
by rewrite ih exterior_word_cons.
Qed.

Section Degree.
Variable m : nat.
Variable Z : lmodType K.
Variable beta : {dffun forall i : 'I_m, power_family V m i} -> Z.
Hypothesis hb : multilinear beta.
Hypothesis ha : alternating_power beta.

Local Notation bw := (beta_words beta).

(** Source for [beta_words_nonuniq]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: Linear maps into degree one of
    an anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma beta_words_nonuniq s : ~~ uniq s -> bw s = 0.
Proof.
move=> hs; rewrite /beta_words; case: eqP => // hm.
by apply: ha; rewrite power_seq_to_power.
Qed.

(** Source for [exterior_degree_lift]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma exterior_degree_lift :
  exists fT : {linear tensor_algebra_space V -> Z},
    (forall s, fT (tensor_word s) = bw s) /\
    (forall x, fT (tensor_degree m x) = fT x) /\
    (forall x, mV V x -> fT x = 0).
Proof.
have [fT [hw [hd _]]] :=
  tensor_power_universal (beta_words_multilinear hb) (@beta_words_zero K V m Z beta).
exists fT; split=> //; split=> //.
move=> x; elim=> [|u w hu ihu hw' ihw|a u hu ihu|s t v].
- exact: linear0.
- by rewrite linearD ihu ihw add0r.
- by rewrite linearZ_LR ihu scaler0.
rewrite hw; apply: beta_words_nonuniq.
by rewrite cat_uniq /= inE eqxx /= !andbF.
Qed.
End Degree.

(** Source for [exterior_quotient_degree_universal]: Federer (1969), 1.3.1,
    p. 14, universal mapping property and its proof. In words: Linear maps
    into degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma exterior_quotient_degree_universal m :
  exterior_degree_universal exterior_quotient_generator (exterior_grading V) m.
Proof.
move=> Z beta hb ha.
have [fT [hw [hd hk]]] := exterior_degree_lift hb ha.
pose f : {linear exterior_algebra V -> Z} := GRing.Linear.clone _ _ _ _
  (quotient_lift (S := mV V) (f := fT) hk) _.
have fE : forall y, f (pi y) = fT y by move=> y; exact: quotient_liftE.
have fw : forall s, f (exterior_word s) = beta_words beta s.
  by move=> s; rewrite /exterior_word fE hw.
exists f; split.
  move=> t; rewrite -[t]quotient_projection_surjective.
  by rewrite (exterior_degree_projection m) fE hd fE.
split.
  move=> x; rewrite /algebra_power word_eval_exterior_generator fw.
  exact: beta_words_power.
move=> g hg hgx; elim/exterior_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite fw; case: (eqVneq (size s) m) => hs.
  rewrite /beta_words hs eqxx -{1}(power_seq_to_power hs)
    -word_eval_exterior_generator.
  exact: hgx.
rewrite beta_words_zero // -hg.
have -> : grade (exterior_grading V) m (exterior_word s) = exterior_degree m (exterior_word s)
  by [].
by rewrite exterior_degree_word (negPf hs) linear0.
Qed.

(** Source for [exterior_quotient_exists]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem exterior_quotient_exists :
  is_exterior_power_algebra exterior_quotient_generator (exterior_grading V).
Proof.
constructor.
- exact: exterior_generator_square.
- move=> m x; rewrite /algebra_power word_eval_exterior_generator.
  by have := exterior_word_homogeneous (power_seq x); rewrite size_power_seq.
- exact: exterior_quotient_degree_universal.
Qed.
End Witness.
