(** Federer (1969), 1.9.1, pp. 41-42: symmetric algebra and its homogeneous
    powers specified by universal properties. The degree-wise universal
    property is the symmetric-multilinear formulation used later in Federer
    1.10.1, pp. 43-44. Arbitrary fields are allowed. This interface contains
    specifications and consequences, no quotient construction or unproved
    existence assumption. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require boolp.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedSums
  ModuleQuotient FamilyUpdate TensorFamilyUP WordEvaluation PowerWords
  TensorAlgebraUP CommutativeWords SymmetricUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Predicate.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.

(** Source for [symmetric_power_function]: Federer 1.9.1, p. 41, spanning
    and universal-property paragraphs; symmetric powers are used in 1.10.1,
    pp. 43-44. In words: Definition: a function of an m-tuple is symmetric
    when permuting its entries preserves its value. *)
Definition symmetric_power_function m (Z : lmodType K)
    (beta : {dffun forall i : 'I_m, power_family V m i} -> Z) : Prop :=
  forall x y, perm_eq (power_seq x) (power_seq y) -> beta x = beta y.

(** Source for [symmetric_degree_universal]: Federer 1.9.1, p. 41, spanning
    and universal-property paragraphs; symmetric powers are used in 1.10.1,
    pp. 43-44. In words: Abstract specification: symmetric m-linear maps
    factor uniquely through the degree-m power. Off-degree values are zero. *)
Definition symmetric_degree_universal m : Prop :=
  forall (Z : lmodType K) (beta : {dffun forall i : 'I_m, power_family V m i} -> Z),
  multilinear beta -> symmetric_power_function beta ->
  exists f : {linear A -> Z},
    (forall t, f (grade G m t) = f t) /\
    (forall x, f (algebra_power iota x) = beta x) /\
    (forall g : {linear A -> Z}, (forall t, g (grade G m t) = g t) ->
      (forall x, g (algebra_power iota x) = beta x) -> forall t, g t = f t).

(** Source for [is_symmetric_power_algebra]: Federer 1.9.1, p. 41, spanning
    and universal-property paragraphs; symmetric powers are used in 1.10.1,
    pp. 43-44. In words: Abstract specification of a commutative algebra
    whose homogeneous powers have the symmetric-multilinear universal
    property. *)
Record is_symmetric_power_algebra : Prop := {
  symmetric_commutative : commutative (alg_mul A);
  symmetric_power_homogeneous : forall m x, homogeneous G m (@algebra_power K V A iota m x);
  symmetric_power_universal : forall m, symmetric_degree_universal m
}.
End Predicate.

Section Consequences.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_symmetric_power_algebra iota G.

(** Source for [sym_word_homogeneous]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting lemma: a word of m generators has degree m. *)
Lemma sym_word_homogeneous (s : seq V) : homogeneous G (size s) (word_eval iota s).
Proof.
have := symmetric_power_homogeneous H (seq_power s).
by rewrite /algebra_power power_seqK.
Qed.

(** Source for [algebra_power_symmetric]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting lemma: composing a product of m generators
    with a linear map gives a symmetric m-linear function. *)
Lemma algebra_power_symmetric m (Z : lmodType K) (g : {linear A -> Z}) :
  symmetric_power_function (fun x => g (@algebra_power K V A iota m x)).
Proof.
move=> x y hxy; congr (g _); rewrite /algebra_power.
exact (@commutative_word_permutation K V A (symmetric_commutative H) iota _ _ hxy).
Qed.

(** Source for [sym_degree_ext]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting uniqueness: linear maps supported in degree
    m are determined by their values on products of m generators. *)
Lemma sym_degree_ext m (Z : lmodType K) (f g : {linear A -> Z}) :
  (forall t, f (grade G m t) = f t) -> (forall t, g (grade G m t) = g t) ->
  (forall x, f (@algebra_power K V A iota m x) = g (algebra_power iota x)) ->
  forall t, f t = g t.
Proof.
move=> hf hg e.
have hm := multilinear_post g
  (multilinear_words_power (m := m) (word_eval_multilinear iota)).
have [h [_ [_ hu]]] := symmetric_power_universal H hm
  (algebra_power_symmetric g).
by move=> t; rewrite (hu f hf e) (hu g hg (fun x => erefl _)).
Qed.

(** Source for [sym_component_span]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The degree-m component is spanned by words in
    generators. *)
Lemma sym_component_span m t : word_combination iota (grade G m t).
Proof.
pose Q := module_quotient (word_subspace iota).
pose p : {linear A -> Q} := linear_comp
  (GRing.Linear.clone _ _ _ _ (quotient_projection (word_subspace iota)) _) (grade G m).
pose z : {linear A -> Q} := GRing.Linear.clone _ _ _ _ (\0 : A -> Q) _.
have hp : forall u, p (grade G m u) = p u.
  by move=> u; rewrite /= grade_orthogonal eqxx.
have e := @sym_degree_ext m _ p z hp (fun u => erefl).
have /quotient_projection_eq : quotient_projection (word_subspace iota) (grade G m t) =
    quotient_projection (word_subspace iota) 0.
  rewrite linear0; apply: e => x /=.
  rewrite (symmetric_power_homogeneous H x).
  rewrite -(linear0 (quotient_projection (word_subspace iota))).
  apply/quotient_projection_eq; rewrite subr0.
  exact: word_combination_word.
by rewrite subr0.
Qed.

(** Source for [sym_algebra_span]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The entire algebra is spanned by finite words,
    including the empty product representing the unit. *)
Theorem sym_algebra_span t : word_combination iota t.
Proof.
elim/(@graded_induction _ _ G): t => [|t u ht hu|n t ht].
- exact: word_combination0.
- exact: word_combinationD.
- by rewrite -ht; exact: sym_component_span.
Qed.

(** Source for [sym_word_induction]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting induction principle from the word spanning
    theorem. *)
Lemma sym_word_induction (P : A -> Prop)
    (h0 : P 0) (hadd : forall t u, P t -> P u -> P (t + u))
    (hscale : forall a t, P t -> P (a *: t))
    (hword : forall s, P (word_eval iota s)) :
  forall t, P t.
Proof.
move=> t; have [s ->] := sym_algebra_span t.
by apply: big_ind => // p _; exact: hscale (hword p.2).
Qed.
End Consequences.

Section Extension.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_symmetric_power_algebra iota G.
Variable B : algebra K.
Variable f : {linear V -> B}.
Hypothesis hf : commutative (alg_mul B).

(** Source for [sym_beta]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting definition: the m-fold product of images in
    a commutative target algebra. *)
Definition sym_beta m (x : {dffun forall i : 'I_m, power_family V m i}) : B :=
  word_eval f (power_seq x).

(** Source for [sym_beta_multilinear]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting lemma: the product of images is multilinear. *)
Lemma sym_beta_multilinear m : multilinear (@sym_beta m).
Proof. exact: multilinear_words_power (word_eval_multilinear f). Qed.

(** Source for [sym_beta_symmetric]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting lemma: the product of images is symmetric. *)
Lemma sym_beta_symmetric m : symmetric_power_function (@sym_beta m).
Proof. move=> x y hxy; exact (@commutative_word_permutation K V B hf f _ _ hxy). Qed.

(** Source for [sym_component_sig]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting choice of the unique degree-m extension,
    using the supplied abstract universal property. *)
Definition sym_component_sig m :=
  boolp.cid (symmetric_power_universal H (@sym_beta_multilinear m)
    (@sym_beta_symmetric m)).

(** Source for [sym_component]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting definition of the unique degree-m extension. *)
Definition sym_component m : {linear A -> B} := proj1_sig (sym_component_sig m).

(** Source for [sym_component_power]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The degree-m extension takes a product of generators to
    the corresponding product of their images. *)
Lemma sym_component_power m x :
  sym_component m (algebra_power iota x) = @sym_beta m x.
Proof. exact: (proj1 (proj2 (proj2_sig (sym_component_sig m)))). Qed.

(** Source for [sym_extension_fun]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Supporting definition assembling the degree extensions
    by the finite graded sum. *)
Definition sym_extension_fun : A -> B := graded_sum G sym_component.
HB.instance Definition _ := GRing.Linear.copy sym_extension_fun
  (graded_sum G sym_component).

(** Source for [sym_extension_word]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The assembled extension takes each word to the word of
    its generator images. *)
Lemma sym_extension_word s : sym_extension_fun (word_eval iota s) = word_eval f s.
Proof.
rewrite /sym_extension_fun (graded_sum_homogeneous _ (sym_word_homogeneous H s)).
have := sym_component_power (seq_power s).
by rewrite /algebra_power /sym_beta power_seqK.
Qed.

(** Source for [sym_extension_one]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The extension preserves the unit, using the empty word. *)
Lemma sym_extension_one : sym_extension_fun (alg_one A) = alg_one B.
Proof. exact: (sym_extension_word [::]). Qed.

(** Source for [sym_extension_mul]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The extension preserves multiplication, by word
    induction. *)
Lemma sym_extension_mul x y :
  sym_extension_fun (alg_mul A x y) =
  alg_mul B (sym_extension_fun x) (sym_extension_fun y).
Proof.
have bA := alg_bilinear A; have bB := alg_bilinear B.
pose g : {linear A -> B} := GRing.Linear.clone _ _ _ _ sym_extension_fun _.
elim/(sym_word_induction H): x y => [|x x' hx hx'|a x hx|s] y.
- by rewrite (bil0l bA) !linear0 (bil0l bB).
- by rewrite (bilDl bA) !linearD /= hx hx' (bilDl bB).
- by rewrite (bilZl bA) !linearZ /= hx (bilZl bB).
elim/(sym_word_induction H): y => [|y y' hy hy'|a y hy|t].
- by rewrite (bil0r bA) !linear0 (bil0r bB).
- by rewrite (bilDr bA) !linearD /= hy hy' (bilDr bB).
- by rewrite (bilZr bA) !linearZ /= hy (bilZr bB).
by rewrite -word_eval_cat !sym_extension_word word_eval_cat.
Qed.

(** Source for [sym_extension]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The resulting unit-preserving algebra homomorphism. *)
Definition sym_extension : algebra_map A B :=
  @AlgebraMap K A B (GRing.Linear.clone _ _ _ _ sym_extension_fun _)
    sym_extension_one sym_extension_mul.

(** Source for [sym_extension_generator]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: The homomorphism extends the given linear map on
    generators. *)
Lemma sym_extension_generator v : sym_extension (iota v) = f v.
Proof.
have := sym_extension_word [:: v].
by rewrite /= alg_unitr alg_unitr.
Qed.

(** Source for [sym_extension_unique]: Federer 1.9.1, p. 41, spanning and
    universal-property paragraphs; symmetric powers are used in 1.10.1, pp.
    43-44. In words: Every algebra homomorphism extending the generator map
    agrees with this extension. *)
Lemma sym_extension_unique (h : algebra_map A B) :
  (forall v, h (iota v) = f v) -> forall t, h t = sym_extension t.
Proof.
move=> hv; elim/(sym_word_induction H) => [|t u ht hu|a t ht|s].
- by rewrite !linear0.
- by rewrite !linearD ht hu.
- by rewrite !linearZ ht.
by rewrite (algebra_map_word hv) /= sym_extension_word.
Qed.
End Extension.

(** Source for [symmetric_power_algebraP]: Federer 1.9.1, p. 41, spanning
    and universal-property paragraphs; symmetric powers are used in 1.10.1,
    pp. 43-44. In words: The degree-wise universal property implies the
    ungraded extension property for commutative targets. This strengthens
    the printed graded statement; grading preservation is proved separately. *)
Theorem symmetric_power_algebraP (K : fieldType) (V : lmodType K)
    (A : algebra K) (iota : {linear V -> A}) (G : grading A) :
  is_symmetric_power_algebra iota G -> is_symmetric_algebra iota.
Proof.
move=> H B hf f; exists (sym_extension H f hf); split.
  exact: sym_extension_generator.
exact: sym_extension_unique.
Qed.
