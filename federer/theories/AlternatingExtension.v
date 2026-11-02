(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import Exterior TensorPowers.
From Federer Require Import Hom HomogeneousHom AlternatingForms AlternatingWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExteriorContexts.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation wb := (wedge_bilinear V).
(** Source for [exterior_word_context_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_word_context_linear s t : linear (fun v : V => exterior_word (s ++ v :: t)).
Proof.
have hw v : exterior_word (s ++ v :: t) =
    wedge (exterior_word s) (wedge (exterior_generator v) (exterior_word t)).
  by rewrite -(@exterior_word_cat K V s (v :: t)) exterior_word_cons.
move=> a v w; rewrite !hw linearP (bilDl wb) (bilZl wb) (bilDr wb) (bilZr wb).
by [].
Qed.
End ExteriorContexts.

(** Federer 1.4.1, first paragraph: g factors through the tensor power;
    its kernel contains mV intersected with that power. Consequently it
    descends to the exterior power. The intermediate maps on the whole
    algebras are zero away from degree m. *)
Section Extension.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).
Local Notation T := (tensor_algebra_space V).
Local Notation A := (A_m V W m).

(** Source for [form_tensor]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition form_tensor (f : A) : {linear T -> W} :=
  multilinear_extension (form_words_multilinear f).
(** Source for [form_tensorE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_tensorE (f : A) s : form_tensor f (tensor_word s) = form_words f s.
Proof. exact: multilinear_extensionE. Qed.

(** Source for [form_ideal_killed]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_ideal_killed (f : A) x : mV V x -> form_tensor f x = 0.
Proof.
elim=> [|z y hz ihz hy ihy|a z hz ihz|s t v].
- exact: linear0.
- by rewrite linearD ihz ihy add0r.
- rewrite linearZ; change (a *: form_tensor f z = 0).
  by rewrite ihz scaler0.
- rewrite form_tensorE; apply: form_words_alternating.
  by rewrite cat_uniq /= mem_head !andbF.
Qed.

(** Source for [form_extension]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition form_extension (f : A) : {linear E -> W} :=
  exterior_word_extension (form_words_multilinear f) (@form_words_alternating K V W m f).
(** Source for [form_extensionE]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_extensionE (f : A) s : form_extension f (exterior_word s) = form_words f s.
Proof. exact: exterior_word_extensionE. Qed.

(** Source for [form_extension_projection]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_extension_projection (f : A) x :
  form_extension f (exterior_projection V x) = form_tensor f x.
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite exterior_projection_word form_extensionE form_tensorE.
Qed.

(** Source for [form_extension_degree]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_extension_degree (f : A) n x :
  n != m -> homogeneous G n x -> form_extension f x = 0.
Proof.
move=> hn; move: x; apply: exterior_component_induction => [|x y hx hy|a x hx|s hs].
- exact: linear0.
- by rewrite linearD hx hy add0r.
- rewrite linearZ; change (a *: form_extension f x = 0).
  by rewrite hx scaler0.
- rewrite form_extensionE; apply: form_words_wrong; by rewrite hs.
Qed.

(** Source for [form_extension_parameter_linear]: Federer (1969), 1.4.1, p.
    17, factorisation paragraph and first displayed isomorphism. In words:
    Every alternating m-linear map factors uniquely through the m-th
    exterior power, giving the isomorphism between forms and linear maps on
    that power. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma form_extension_parameter_linear x : linear (fun f : A => form_extension f x).
Proof.
move=> a f g; elim/exterior_word_induction: x => [|x y hx hy|b x hx|s].
- by rewrite !linear0 add0r.
- rewrite (linearD (form_extension (a *: f + g)))
    (linearD (form_extension f)) (linearD (form_extension g)).
  change (form_extension (a *: f + g) x + form_extension (a *: f + g) y =
    a *: (form_extension f x + form_extension f y) +
      (form_extension g x + form_extension g y)).
  by rewrite hx hy scalerDr addrACA.
- rewrite (linZ (linearP (form_extension (a *: f + g))) b x)
    (linZ (linearP (form_extension f)) b x)
    (linZ (linearP (form_extension g)) b x).
  change (b *: form_extension (a *: f + g) x =
    a *: (b *: form_extension f x) + b *: form_extension g x).
  by rewrite hx scalerDr !scalerA [b * a]mulrC.
- rewrite !form_extensionE; exact: form_words_linear.
Qed.

(** Source for [form_homogeneous]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition form_homogeneous (f : A) : Hom_m W G m :=
  @HomogeneousHom K E W G m (hom_of_linear (form_extension f))
    (introT (asboolP _) (@form_extension_degree f)).
(** Source for [form_homogeneousE]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_homogeneousE f x : form_homogeneous f x = form_extension f x.
Proof. by []. Qed.
(** Source for [form_homogeneous_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_homogeneous_linear : linear form_homogeneous.
Proof.
move=> a f g; apply: hom_m_ext => x.
rewrite hom_m_addE hom_m_scaleE !form_homogeneousE.
exact: form_extension_parameter_linear.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K A (Hom_m W G m)
  *:%R form_homogeneous form_homogeneous_linear.

(** Source for [form_tensor_power]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition form_tensor_power (f : A) : {linear graded_component (tensor_grading V) m -> W} :=
  linear_comp (form_tensor f)
    (GRing.Linear.clone _ _ _ _ (@component_val K T (tensor_grading V) m) _).
(** Source for [form_power_relation_killed]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_power_relation_killed (f : A) x : exterior_power_subspace V m x ->
  form_tensor_power f x = 0.
Proof. exact: form_ideal_killed. Qed.
End Extension.
