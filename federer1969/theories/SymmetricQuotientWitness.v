(** Federer (1969), 1.9.1, p. 41, and 1.10.1, pp. 43-44: the private tensor
    quotient satisfies the symmetric-power universal property. This proves
    existence for the subsequent sealed interface. No finite-dimensional or
    characteristic restriction. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP GradedAlgebra
  FamilyUpdate TensorFamilyUP WordEvaluation PowerWords TensorAlgebraUP
  TensorAlgebra TensorGrading TensorPowers AlgebraQuotient SymmetricIdeal
  SymmetricAlgebraUP SymmetricQuotient SymmetricQuotientGrading SymmetricQuotientPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Witness.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation pi := (quotient_projection (commutator_ideal V)).

(** Source for [symmetric_quotient_generator]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The generating linear map into
    the private tensor quotient. *)
Definition symmetric_quotient_generator : {linear V -> symmetric_algebra V} :=
  GRing.Linear.clone _ _ _ _ (@symmetric_generator K V) _.

(** Source for [word_eval_symmetric_generator]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: Evaluating generators in the
    quotient agrees with projecting the tensor word. *)
Lemma word_eval_symmetric_generator s :
  word_eval symmetric_quotient_generator s = symmetric_word s.
Proof.
elim: s => [|v s ih] //=.
by rewrite ih symmetric_word_cons.
Qed.

Section Degree.
Variable m : nat.
Variable Z : lmodType K.
Variable beta : {dffun forall i : 'I_m, power_family V m i} -> Z.
Hypothesis hb : multilinear beta.
Hypothesis ha : symmetric_power_function beta.

Local Notation bw := (beta_words beta).

(** Source for [symmetric_beta_words_permutation]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The fixed-degree extension of a
    symmetric tuple function is invariant under word permutation. *)
Lemma symmetric_beta_words_permutation s t :
  perm_eq s t -> bw s = bw t.
Proof.
move=> hp; have hsiz := perm_size hp.
rewrite /beta_words; case: eqP => hs; case: eqP => ht => //.
- apply: ha; by rewrite !power_seq_to_power.
- by exfalso; apply: ht; rewrite -hsiz.
- by exfalso; apply: hs; rewrite hsiz.
Qed.

(** Source for [symmetric_degree_lift]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: A symmetric multilinear function extends to
    the tensor algebra and kills the commutator ideal. *)
Lemma symmetric_degree_lift :
  exists fT : {linear tensor_algebra_space V -> Z},
    (forall s, fT (tensor_word s) = bw s) /\
    (forall x, fT (tensor_degree m x) = fT x) /\
    (forall x, commutator_ideal V x -> fT x = 0).
Proof.
have [fT [hw [hd _]]] :=
  tensor_power_universal (beta_words_multilinear hb) (@beta_words_zero K V m Z beta).
exists fT; split=> //; split=> //.
move=> x; elim=> [|u w hu ihu hw' ihw|a u hu ihu|s t v w].
- exact: linear0.
- by rewrite linearD ihu ihw add0r.
- by rewrite linearZ_LR ihu scaler0.
rewrite linearB !hw.
have hp : perm_eq (s ++ v :: w :: t) (s ++ w :: v :: t).
  by rewrite perm_cat2l -[v :: w :: t]/([:: v] ++ [:: w] ++ t) perm_catCA.
by rewrite (symmetric_beta_words_permutation hp) subrr.
Qed.
End Degree.

(** Source for [symmetric_quotient_degree_universal]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: Every symmetric m-linear
    function factors uniquely through the quotient degree-m power. *)
Lemma symmetric_quotient_degree_universal m :
  symmetric_degree_universal symmetric_quotient_generator (symmetric_grading V) m.
Proof.
move=> Z beta hb ha.
have [fT [hw [hd hk]]] := symmetric_degree_lift hb ha.
pose f : {linear symmetric_algebra V -> Z} := GRing.Linear.clone _ _ _ _
  (quotient_lift (S := commutator_ideal V) (f := fT) hk) _.
have fE : forall y, f (pi y) = fT y by move=> y; exact: quotient_liftE.
have fw : forall s, f (symmetric_word s) = beta_words beta s.
  by move=> s; rewrite /symmetric_word fE hw.
exists f; split.
  move=> t; rewrite -[t]quotient_projection_surjective.
  by rewrite (symmetric_degree_projection m) fE hd fE.
split.
  move=> x; rewrite /algebra_power word_eval_symmetric_generator fw.
  exact: beta_words_power.
move=> g hg hgx; elim/symmetric_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite fw; case: (eqVneq (size s) m) => hs.
  rewrite /beta_words hs eqxx -{1}(power_seq_to_power hs)
    -word_eval_symmetric_generator.
  exact: hgx.
rewrite beta_words_zero // -hg.
have -> : grade (symmetric_grading V) m (symmetric_word s) = symmetric_degree m (symmetric_word s)
  by [].
by rewrite symmetric_degree_word (negPf hs) linear0.
Qed.

(** Source for [symmetric_quotient_exists]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The tensor quotient satisfies the full
    abstract symmetric-power algebra specification. *)
Theorem symmetric_quotient_exists :
  is_symmetric_power_algebra symmetric_quotient_generator (symmetric_grading V).
Proof.
constructor.
- exact: symmetric_product_commute.
- move=> m x; rewrite /algebra_power word_eval_symmetric_generator.
  by have := symmetric_word_homogeneous (power_seq x); rewrite size_power_seq.
- exact: symmetric_quotient_degree_universal.
Qed.
End Witness.
