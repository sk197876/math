(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require boolp.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedSums
  ModuleQuotient FamilyUpdate TensorFamilyUP WordEvaluation PowerWords
  TensorAlgebraUP SquareZeroWords ExteriorUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1 and 1.4.1 as a property. A graded associative unital
    algebra A with a linear map ι : V → A is an exterior algebra of V if
    ι(v) ι(v) = 0, the product ι(v_1) ⋯ ι(v_m) has degree m, and the degree-m
    component has the universal property for alternating m-linear maps. A
    linear map on the component is represented by a linear map on A
    vanishing off degree m. *)
Section Predicate.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.

(** Source for [alternating_power]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: Linear maps into degree one of
    an anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Definition or construction used
    to formalise this passage. *)
Definition alternating_power m (Z : lmodType K)
    (beta : {dffun forall i : 'I_m, power_family V m i} -> Z) : Prop :=
  forall x, ~~ uniq (power_seq x) -> beta x = 0.

(** Source for [exterior_degree_universal]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Definition
    or construction used to formalise this passage. *)
Definition exterior_degree_universal m : Prop :=
  forall (Z : lmodType K) (beta : {dffun forall i : 'I_m, power_family V m i} -> Z),
  multilinear beta -> alternating_power beta ->
  exists f : {linear A -> Z},
    (forall t, f (grade G m t) = f t) /\
    (forall x, f (algebra_power iota x) = beta x) /\
    (forall g : {linear A -> Z}, (forall t, g (grade G m t) = g t) ->
      (forall x, g (algebra_power iota x) = beta x) -> forall t, g t = f t).

(** Source for [is_exterior_power_algebra]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Record is_exterior_power_algebra : Prop := {
  exterior_square : forall v, alg_mul A (iota v) (iota v) = 0;
  exterior_power_homogeneous : forall m x, homogeneous G m (@algebra_power K V A iota m x);
  exterior_power_universal : forall m, exterior_degree_universal m
}.
End Predicate.

Section Consequences.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_exterior_power_algebra iota G.

(** Source for [alt_word_homogeneous]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma alt_word_homogeneous (s : seq V) : homogeneous G (size s) (word_eval iota s).
Proof.
have := exterior_power_homogeneous H (seq_power s).
by rewrite /algebra_power power_seqK.
Qed.

(** Source for [algebra_power_alternating]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma algebra_power_alternating m (Z : lmodType K) (g : {linear A -> Z}) :
  alternating_power (fun x => g (@algebra_power K V A iota m x)).
Proof.
move=> x hx; rewrite /algebra_power.
by rewrite (square_zero_word_nonuniq (exterior_square H) hx) linear0.
Qed.

(** Source for [alt_degree_ext]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma alt_degree_ext m (Z : lmodType K) (f g : {linear A -> Z}) :
  (forall t, f (grade G m t) = f t) -> (forall t, g (grade G m t) = g t) ->
  (forall x, f (@algebra_power K V A iota m x) = g (algebra_power iota x)) ->
  forall t, f t = g t.
Proof.
move=> hf hg e.
have hm := multilinear_post g
  (multilinear_words_power (m := m) (word_eval_multilinear iota)).
have [h [_ [_ hu]]] := exterior_power_universal H hm
  (algebra_power_alternating g).
by move=> t; rewrite (hu f hf e) (hu g hg (fun x => erefl _)).
Qed.

(** Source for [alt_component_span]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma alt_component_span m t : word_combination iota (grade G m t).
Proof.
pose Q := module_quotient (word_subspace iota).
pose p : {linear A -> Q} := linear_comp
  (GRing.Linear.clone _ _ _ _ (quotient_projection (word_subspace iota)) _) (grade G m).
pose z : {linear A -> Q} := GRing.Linear.clone _ _ _ _ (\0 : A -> Q) _.
have hp : forall u, p (grade G m u) = p u.
  by move=> u; rewrite /= grade_orthogonal eqxx.
have e := @alt_degree_ext m _ p z hp (fun u => erefl).
have /quotient_projection_eq : quotient_projection (word_subspace iota) (grade G m t) =
    quotient_projection (word_subspace iota) 0.
  rewrite linear0; apply: e => x /=.
  rewrite (exterior_power_homogeneous H x).
  rewrite -(linear0 (quotient_projection (word_subspace iota))).
  apply/quotient_projection_eq; rewrite subr0.
  exact: word_combination_word.
by rewrite subr0.
Qed.

(** Source for [alt_algebra_span]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: Linear maps into degree one of
    an anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem alt_algebra_span t : word_combination iota t.
Proof.
elim/(@graded_induction _ _ G): t => [|t u ht hu|n t ht].
- exact: word_combination0.
- exact: word_combinationD.
- by rewrite -ht; exact: alt_component_span.
Qed.

(** Source for [alt_word_induction]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: Linear maps into degree one of
    an anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma alt_word_induction (P : A -> Prop)
    (h0 : P 0) (hadd : forall t u, P t -> P u -> P (t + u))
    (hscale : forall a t, P t -> P (a *: t))
    (hword : forall s, P (word_eval iota s)) :
  forall t, P t.
Proof.
move=> t; have [s ->] := alt_algebra_span t.
by apply: big_ind => // p _; exact: hscale (hword p.2).
Qed.
End Consequences.

(** Every linear map f : V → B with f(v) f(v) = 0 extends uniquely to an
    algebra map; the extension is assembled degree by degree. *)
Section Extension.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.
Variable G : grading A.
Hypothesis H : is_exterior_power_algebra iota G.
Variable B : algebra K.
Variable f : {linear V -> B}.
Hypothesis hf : forall v, alg_mul B (f v) (f v) = 0.

(** Source for [alt_beta]: Federer (1969), 1.3.1, p. 14, universal mapping
    property and its proof. In words: Linear maps into degree one of an
    anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Definition or construction used
    to formalise this passage. *)
Definition alt_beta m (x : {dffun forall i : 'I_m, power_family V m i}) : B :=
  word_eval f (power_seq x).

(** Source for [alt_beta_multilinear]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma alt_beta_multilinear m : multilinear (@alt_beta m).
Proof. exact: multilinear_words_power (word_eval_multilinear f). Qed.

(** Source for [alt_beta_alternating]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma alt_beta_alternating m : alternating_power (@alt_beta m).
Proof. by move=> x hx; rewrite /alt_beta (square_zero_word_nonuniq hf hx). Qed.

(** Source for [alt_component_sig]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition alt_component_sig m :=
  boolp.cid (exterior_power_universal H (@alt_beta_multilinear m)
    (@alt_beta_alternating m)).

(** Source for [alt_component]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition alt_component m : {linear A -> B} := proj1_sig (alt_component_sig m).

(** Source for [alt_component_power]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma alt_component_power m x :
  alt_component m (algebra_power iota x) = @alt_beta m x.
Proof. exact: (proj1 (proj2 (proj2_sig (alt_component_sig m)))). Qed.

(** Source for [alt_extension_fun]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: The tensor-algebra extension
    factors through the exterior quotient precisely when the images of the
    generators have square zero. Definition or construction used to
    formalise this passage. The square-zero target condition is used in the
    proof on p. 14. The abstract ungraded square-zero property formalised
    here is stronger than the printed graded anticommutative formulation and
    also works in characteristic two. *)
Definition alt_extension_fun : A -> B := graded_sum G alt_component.
HB.instance Definition _ := GRing.Linear.copy alt_extension_fun
  (graded_sum G alt_component).

(** Source for [alt_extension_word]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: The tensor-algebra extension
    factors through the exterior quotient precisely when the images of the
    generators have square zero. Supporting lemma for this passage; not
    separately stated in the book. The square-zero target condition is used
    in the proof on p. 14. The abstract ungraded square-zero property
    formalised here is stronger than the printed graded anticommutative
    formulation and also works in characteristic two. *)
Lemma alt_extension_word s : alt_extension_fun (word_eval iota s) = word_eval f s.
Proof.
rewrite /alt_extension_fun (graded_sum_homogeneous _ (alt_word_homogeneous H s)).
have := alt_component_power (seq_power s).
by rewrite /algebra_power /alt_beta power_seqK.
Qed.

(** Source for [alt_extension_one]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: The tensor-algebra extension
    factors through the exterior quotient precisely when the images of the
    generators have square zero. Supporting lemma for this passage; not
    separately stated in the book. The square-zero target condition is used
    in the proof on p. 14. The abstract ungraded square-zero property
    formalised here is stronger than the printed graded anticommutative
    formulation and also works in characteristic two. *)
Lemma alt_extension_one : alt_extension_fun (alg_one A) = alg_one B.
Proof. exact: (alt_extension_word [::]). Qed.

(** Source for [alt_extension_mul]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: The tensor-algebra extension
    factors through the exterior quotient precisely when the images of the
    generators have square zero. Supporting lemma for this passage; not
    separately stated in the book. The square-zero target condition is used
    in the proof on p. 14. The abstract ungraded square-zero property
    formalised here is stronger than the printed graded anticommutative
    formulation and also works in characteristic two. *)
Lemma alt_extension_mul x y :
  alt_extension_fun (alg_mul A x y) =
  alg_mul B (alt_extension_fun x) (alt_extension_fun y).
Proof.
have bA := alg_bilinear A; have bB := alg_bilinear B.
pose g : {linear A -> B} := GRing.Linear.clone _ _ _ _ alt_extension_fun _.
elim/(alt_word_induction H): x y => [|x x' hx hx'|a x hx|s] y.
- by rewrite (bil0l bA) !linear0 (bil0l bB).
- by rewrite (bilDl bA) !linearD /= hx hx' (bilDl bB).
- by rewrite (bilZl bA) !linearZ /= hx (bilZl bB).
elim/(alt_word_induction H): y => [|y y' hy hy'|a y hy|t].
- by rewrite (bil0r bA) !linear0 (bil0r bB).
- by rewrite (bilDr bA) !linearD /= hy hy' (bilDr bB).
- by rewrite (bilZr bA) !linearZ /= hy (bilZr bB).
by rewrite -word_eval_cat !alt_extension_word word_eval_cat.
Qed.

(** Source for [alt_extension]: Federer (1969), 1.3.1, p. 14, universal
    mapping property and its proof. In words: Linear maps into degree one of
    an anticommutative associative unital graded algebra extend uniquely to
    unit-preserving graded algebra maps; square-zero images make the tensor
    extension factor through the quotient. Definition or construction used
    to formalise this passage. *)
Definition alt_extension : algebra_map A B :=
  @AlgebraMap K A B (GRing.Linear.clone _ _ _ _ alt_extension_fun _)
    alt_extension_one alt_extension_mul.

(** Source for [alt_extension_generator]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Supporting lemma for this
    passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Lemma alt_extension_generator v : alt_extension (iota v) = f v.
Proof.
have := alt_extension_word [:: v].
by rewrite /= alg_unitr alg_unitr.
Qed.

(** Source for [alt_extension_unique]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Supporting lemma for this
    passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Lemma alt_extension_unique (h : algebra_map A B) :
  (forall v, h (iota v) = f v) -> forall t, h t = alt_extension t.
Proof.
move=> hv; elim/(alt_word_induction H) => [|t u ht hu|a t ht|s].
- by rewrite !linear0.
- by rewrite !linearD ht hu.
- by rewrite !linearZ ht.
by rewrite (algebra_map_word hv) /= alt_extension_word.
Qed.
End Extension.

(** Source for [exterior_power_algebraP]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The
    square-zero target condition is used in the proof on p. 14. The abstract
    ungraded square-zero property formalised here is stronger than the
    printed graded anticommutative formulation and also works in
    characteristic two. *)
Theorem exterior_power_algebraP (K : fieldType) (V : lmodType K)
    (A : algebra K) (iota : {linear V -> A}) (G : grading A) :
  is_exterior_power_algebra iota G -> is_exterior_algebra iota.
Proof.
move=> H; split; first exact: exterior_square H.
move=> B f hf; exists (alt_extension H hf); split.
  exact: alt_extension_generator.
exact: alt_extension_unique.
Qed.
