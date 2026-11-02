(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finfun.
From Federer Require Import ExteriorCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [product_index_enum]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma product_index_enum (I : finType) : index_enum I = enum I.
Proof. by rewrite /index_enum unlock enumT. Qed.

(** Federer 1.3.4, expansion of f(e_1) wedge ... wedge f(e_n).
    The following distributive laws apply to arbitrary finite families. *)
Section Products.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation mu := (@wedge K V).
Local Notation u := (exterior_unit V).
Local Notation wb := (wedge_bilinear V).

HB.instance Definition _ := Monoid.isLaw.Build E u mu
  (@wedge_assoc K V) (@wedge_unitl K V) (@wedge_unitr K V).
HB.instance Definition _ := Monoid.isMulLaw.Build E (0 : E) mu
  (bil0l wb) (bil0r wb).
(** Source for [exterior_add]: Federer (1969), 1.3.4, p. 16, basis expansion
    and signed permutation formula. In words: Expanding the images of a
    basis in the top exterior power yields the determinant as the signed sum
    of products of coefficients, indexed by permutations. Definition or
    construction used to formalise this passage. *)
Definition exterior_add (x y : E) := x + y.
HB.instance Definition _ := Monoid.isComLaw.Build E (0 : E) exterior_add
  (@addrA E) (@addrC E) (@add0r E).
HB.instance Definition _ := Monoid.isAddLaw.Build E mu exterior_add
  (bilDl wb) (bilDr wb).

(** Source for [exterior_word_bigop]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_word_bigop (s : seq V) :
  exterior_word s = \big[mu/u]_(v <- s) exterior_generator v.
Proof. by elim: s => [|v s ih]; rewrite ?big_nil ?big_cons ?exterior_word_nil ?exterior_word_cons ?ih. Qed.

(** Source for [exterior_word_scaled]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_word_scaled (I : Type) (s : seq I) (a : I -> K) (e : I -> V) :
  exterior_word [seq a i *: e i | i <- s] =
    (\prod_(i <- s) a i) *: exterior_word [seq e i | i <- s].
Proof.
elim: s => [|i s ih]; first by rewrite /= big_nil scale1r.
by rewrite /= big_cons !exterior_word_cons linearZ ih (bilZl wb) (bilZr wb) scalerA.
Qed.

(** Source for [exterior_word_expansion]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem exterior_word_expansion (I J : finType) (a : I -> J -> K) (e : J -> V) :
  exterior_word [seq \sum_(j : J) a i j *: e j | i <- enum I] =
    \sum_(f : {ffun I -> J}) (\prod_(i : I) a i (f i)) *:
      exterior_word [seq e (f i) | i <- enum I].
Proof.
rewrite exterior_word_bigop big_map -(product_index_enum I).
transitivity (\big[mu/u]_(i : I) \sum_(j : J) a i j *: exterior_generator (e j)).
- apply: eq_bigr => i _; rewrite linear_sum.
  apply: eq_bigr => j _; exact: linearZ.
- have hd := @bigA_distr_bigA E (0 : E) u
    (Monoid.MulLaw.clone E (0 : E) mu _)
    (Monoid.AddLaw.clone E (0 : E) mu exterior_add _)
    I J (fun i j => a i j *: exterior_generator (e j)).
  apply: eq_trans hd _; apply: eq_bigr => f _.
  rewrite -exterior_word_scaled exterior_word_bigop big_map.
  apply: eq_bigr => i _; symmetry; exact: linearZ.
Qed.

(** Federer 1.3.4: terms with a repeated index vanish. This follows from
    the defining square relation, including in characteristic two. *)
(** Source for [exterior_word_repeat]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma exterior_word_repeat v (s t : seq V) :
  exterior_word (v :: s ++ v :: t) = 0.
Proof.
rewrite (@exterior_word_cons K V v (s ++ v :: t)).
change (wedge (exterior_generator v) (exterior_word (s ++ v :: t)) = 0).
rewrite -(@exterior_word_cat K V s (v :: t)) (@exterior_word_cons K V v t)
  wedge_assoc exterior_generator_word (bilZl wb) -wedge_assoc
  (@wedge_assoc K V (exterior_generator v) (exterior_generator v) (exterior_word t))
  exterior_generator_square (bil0l wb) (bil0r wb) scaler0.
by [].
Qed.

(** Source for [exterior_word_nonuniq]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma exterior_word_nonuniq (s : seq V) : ~~ uniq s -> exterior_word s = 0.
Proof.
elim: s => [|v s ih] //=.
case hv: (v \in s) => /=.
- move=> _; case/splitPr: hv => s1 s2.
  exact: exterior_word_repeat.
- move=> hs; by rewrite exterior_word_cons (ih hs) (bil0r wb).
Qed.

(** Source for [exterior_word_map_nonuniq]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma exterior_word_map_nonuniq (I : eqType) (e : I -> V) (s : seq I) :
  ~~ uniq s -> exterior_word [seq e i | i <- s] = 0.
Proof.
move=> hs; apply: exterior_word_nonuniq.
apply: contra hs => hm; exact: map_uniq hm.
Qed.
End Products.
