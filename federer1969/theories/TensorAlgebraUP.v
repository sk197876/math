(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedSums
  ModuleQuotient FamilyUpdate TensorFamilyUP WordEvaluation PowerWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3 as a property. A graded associative unital algebra A with
    a linear map ι : V → A is a tensor algebra of V if, for every m, the
    product (v_1, …, v_m) ↦ ι(v_1) ⋯ ι(v_m) takes values of degree m and
    makes the degree-m component a tensor product of m copies of V. A linear
    map on the component is represented by a linear map on A vanishing off
    degree m. *)
Section Predicate.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.

(** Source for [algebra_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition algebra_power m (x : {dffun forall i : 'I_m, power_family V m i}) : A :=
  word_eval iota (power_seq x).

(** Source for [degree_universal]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition degree_universal m : Prop :=
  forall (Z : lmodType K) (beta : {dffun forall i : 'I_m, power_family V m i} -> Z),
  multilinear beta ->
  exists f : {linear A -> Z},
    (forall t, f (grade G m t) = f t) /\
    (forall x, f (algebra_power x) = beta x) /\
    (forall g : {linear A -> Z}, (forall t, g (grade G m t) = g t) ->
      (forall x, g (algebra_power x) = beta x) -> forall t, g t = f t).

(** Source for [is_graded_tensor_algebra]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Definition or construction used to
    formalise this passage. *)
Record is_graded_tensor_algebra : Prop := {
  power_homogeneous : forall m x, homogeneous G m (@algebra_power m x);
  power_universal : forall m, degree_universal m
}.
End Predicate.

Section Consequences.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_graded_tensor_algebra iota G.

(** Source for [word_homogeneous]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_homogeneous (s : seq V) : homogeneous G (size s) (word_eval iota s).
Proof.
have := power_homogeneous H (seq_power s).
by rewrite /algebra_power power_seqK.
Qed.

(** Source for [algebra_power_multilinear]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma algebra_power_multilinear m : multilinear (@algebra_power K V A iota m).
Proof. exact: multilinear_words_power (word_eval_multilinear iota). Qed.

(** Source for [degree_ext]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma degree_ext m (Z : lmodType K) (f g : {linear A -> Z}) :
  (forall t, f (grade G m t) = f t) -> (forall t, g (grade G m t) = g t) ->
  (forall x, f (@algebra_power K V A iota m x) = g (algebra_power iota x)) ->
  forall t, f t = g t.
Proof.
move=> hf hg e.
have [h [_ [_ hu]]] := power_universal H
  (multilinear_post g (@algebra_power_multilinear m)).
by move=> t; rewrite (hu f hf e) (hu g hg (fun x => erefl _)).
Qed.

(** Source for [word_combination]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_combination (t : A) : Prop :=
  exists s : seq (K * seq V), t = \sum_(p <- s) p.1 *: word_eval iota p.2.

(** Source for [word_combination0]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_combination0 : word_combination 0.
Proof. by exists [::]; rewrite big_nil. Qed.

(** Source for [word_combinationD]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_combinationD t u :
  word_combination t -> word_combination u -> word_combination (t + u).
Proof. by move=> [s ->] [r ->]; exists (s ++ r); rewrite big_cat. Qed.

(** Source for [word_combinationZ]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_combinationZ a t : word_combination t -> word_combination (a *: t).
Proof.
move=> [s ->]; exists [seq (a * p.1, p.2) | p <- s].
rewrite big_map scaler_sumr; apply: eq_bigr => p _.
by rewrite scalerA.
Qed.

(** Source for [word_subspace]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_subspace : subspace A :=
  @Subspace K A word_combination word_combination0 word_combinationD
    word_combinationZ.

(** Source for [word_combination_word]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_combination_word s : word_combination (word_eval iota s).
Proof. by exists [:: (1, s)]; rewrite big_seq1 scale1r. Qed.

(** Each homogeneous component is spanned by the m-fold products; the proof
    uses only the universal property of that component. *)
(** Source for [component_span]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma component_span m t : word_combination (grade G m t).
Proof.
pose Q := module_quotient word_subspace.
pose p : {linear A -> Q} := linear_comp
  (GRing.Linear.clone _ _ _ _ (quotient_projection word_subspace) _) (grade G m).
pose z : {linear A -> Q} := GRing.Linear.clone _ _ _ _ (\0 : A -> Q) _.
have hp : forall u, p (grade G m u) = p u.
  by move=> u; rewrite /= grade_orthogonal eqxx.
have e := @degree_ext m _ p z hp (fun u => erefl).
have /quotient_projection_eq : quotient_projection word_subspace (grade G m t) =
    quotient_projection word_subspace 0.
  rewrite linear0; apply: e => x /=.
  rewrite (power_homogeneous H x) -(linear0 (quotient_projection word_subspace)).
  apply/quotient_projection_eq; rewrite subr0.
  exact: word_combination_word.
by rewrite subr0.
Qed.

(** Source for [tensor_algebra_span]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_algebra_span t : word_combination t.
Proof.
elim/(@graded_induction _ _ G): t => [|t u ht hu|n t ht].
- exact: word_combination0.
- exact: word_combinationD.
- by rewrite -ht; exact: component_span.
Qed.

(** Source for [word_induction]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_induction (P : A -> Prop)
    (h0 : P 0) (hadd : forall t u, P t -> P u -> P (t + u))
    (hscale : forall a t, P t -> P (a *: t))
    (hword : forall s, P (word_eval iota s)) :
  forall t, P t.
Proof.
move=> t; have [s ->] := tensor_algebra_span t.
by apply: big_ind => // p _; exact: hscale (hword p.2).
Qed.
End Consequences.

(** Every linear map f : V → B into an associative unital algebra extends
    uniquely to an algebra map; the extension is assembled degree by degree
    from the universal properties of the components. *)
Section Extension.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_graded_tensor_algebra iota G.
Variable B : algebra K.
Variable f : {linear V -> B}.

(** Source for [extension_beta]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Definition or
    construction used to formalise this passage. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Definition extension_beta m (x : {dffun forall i : 'I_m, power_family V m i}) : B :=
  word_eval f (power_seq x).

(** Source for [extension_beta_multilinear]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma extension_beta_multilinear m : multilinear (@extension_beta m).
Proof. exact: multilinear_words_power (word_eval_multilinear f). Qed.

(** Source for [extension_component_sig]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Definition or construction used to formalise this passage. The ungraded
    universal property is a local strengthening; it is not the literal
    graded property stated in this passage. *)
Definition extension_component_sig m :=
  boolp.cid (power_universal H (@extension_beta_multilinear m)).

(** Source for [extension_component]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Definition or
    construction used to formalise this passage. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Definition extension_component m : {linear A -> B} :=
  proj1_sig (extension_component_sig m).

(** Source for [extension_component_power]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma extension_component_power m x :
  extension_component m (algebra_power iota x) = @extension_beta m x.
Proof. exact: (proj1 (proj2 (proj2_sig (extension_component_sig m)))). Qed.

(** Source for [graded_extension_fun]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Definition or
    construction used to formalise this passage. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Definition graded_extension_fun : A -> B := graded_sum G extension_component.
HB.instance Definition _ := GRing.Linear.copy graded_extension_fun
  (graded_sum G extension_component).

(** Source for [graded_extension_word]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma graded_extension_word s : graded_extension_fun (word_eval iota s) = word_eval f s.
Proof.
rewrite /graded_extension_fun (graded_sum_homogeneous _ (word_homogeneous H s)).
have := extension_component_power (seq_power s).
by rewrite /algebra_power /extension_beta power_seqK.
Qed.

(** Source for [graded_extension_one]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma graded_extension_one : graded_extension_fun (alg_one A) = alg_one B.
Proof. exact: (graded_extension_word [::]). Qed.

(** Source for [graded_extension_mul]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma graded_extension_mul x y :
  graded_extension_fun (alg_mul A x y) =
  alg_mul B (graded_extension_fun x) (graded_extension_fun y).
Proof.
have bA := alg_bilinear A; have bB := alg_bilinear B.
pose g : {linear A -> B} := GRing.Linear.clone _ _ _ _ graded_extension_fun _.
elim/(word_induction H): x y => [|x x' hx hx'|a x hx|s] y.
- by rewrite (bil0l bA) !linear0 (bil0l bB).
- by rewrite (bilDl bA) !linearD /= hx hx' (bilDl bB).
- by rewrite (bilZl bA) !linearZ /= hx (bilZl bB).
elim/(word_induction H): y => [|y y' hy hy'|a y hy|t].
- by rewrite (bil0r bA) !linear0 (bil0r bB).
- by rewrite (bilDr bA) !linearD /= hy hy' (bilDr bB).
- by rewrite (bilZr bA) !linearZ /= hy (bilZr bB).
by rewrite -word_eval_cat !graded_extension_word word_eval_cat.
Qed.

(** Source for [graded_extension]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition graded_extension : algebra_map A B :=
  @AlgebraMap K A B (GRing.Linear.clone _ _ _ _ graded_extension_fun _)
    graded_extension_one graded_extension_mul.

(** Source for [graded_extension_generator]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma graded_extension_generator v : graded_extension (iota v) = f v.
Proof.
have := graded_extension_word [:: v].
by rewrite /= alg_unitr alg_unitr.
Qed.

(** Source for [algebra_map_word]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma algebra_map_word (h : algebra_map A B) :
  (forall v, h (iota v) = f v) -> forall s, h (word_eval iota s) = word_eval f s.
Proof.
move=> hv; elim=> [|v s ih] /=; first exact: algebra_map_one.
by rewrite algebra_map_mul hv ih.
Qed.

(** Source for [graded_extension_unique]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma graded_extension_unique (h : algebra_map A B) :
  (forall v, h (iota v) = f v) -> forall t, h t = graded_extension t.
Proof.
move=> hv; elim/(word_induction H) => [|t u ht hu|a t ht|s].
- by rewrite !linear0.
- by rewrite !linearD ht hu.
- by rewrite !linearZ ht.
by rewrite (algebra_map_word hv) /= graded_extension_word.
Qed.
End Extension.

(** Source for [graded_tensor_algebraP]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem graded_tensor_algebraP (K : fieldType) (V : lmodType K)
    (A : algebra K) (iota : {linear V -> A}) (G : grading A) :
  is_graded_tensor_algebra iota G -> is_tensor_algebra iota.
Proof.
move=> H B f; exists (graded_extension H f); split.
  exact: graded_extension_generator.
exact: graded_extension_unique.
Qed.
