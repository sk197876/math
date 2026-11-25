(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP GradedAlgebra GradedSums GradedComponents.
From Federer Require Import Hom HomogeneousHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, the direct sum of Hom^m: its elements have only finitely
    many nonzero homogeneous restrictions. This is a direct sum, even
    when the underlying vector spaces have infinite dimension. *)
Section BoundedMaps.
Variable K : fieldType.
Variables V W : lmodType K.
Variable G : grading V.
Local Notation H := (GRing.Lmodule.clone K (Hom V W) _).
(** Source for [hom_bounded]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition hom_bounded (f : Hom V W) N : Prop :=
  forall n x, (N <= n)%N -> homogeneous G n x -> f x = 0.
(** Source for [hom_finite_pred]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition hom_finite_pred (f : Hom V W) := `[< exists N, hom_bounded f N >].
(** Source for [Hom_finite]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Record Hom_finite := FiniteHom {
  hom_finite_val : Hom V W;
  hom_finite_proof : hom_finite_pred hom_finite_val
}.
Coercion hom_finite_val : Hom_finite >-> Hom.
(** Source for [hom_finite_rect]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition hom_finite_rect (P : Hom_finite -> Type)
    (h : forall f hf, P (@FiniteHom f hf)) (z : Hom_finite) : P z :=
  match z as z' return P z' with @FiniteHom f hf => h f hf end.
HB.instance Definition _ := [isSub for hom_finite_val by hom_finite_rect].
HB.instance Definition _ := [Choice of Hom_finite by <:].
(** Source for [hom_finite_closed]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_closed : GRing.submod_closed hom_finite_pred.
Proof.
split.
- apply/asboolP; exists 0%N; by move=> n x hn hx; rewrite hom_zeroE.
- move=> a f g /asboolP [N hN] /asboolP [M hM]; apply/asboolP.
  exists (maxn N M); move=> n x hn hx.
  have /andP [hNn hMn] : (N <= n)%N && (M <= n)%N by rewrite -geq_max.
  by rewrite hom_addE hom_scaleE (hN n x hNn hx) (hM n x hMn hx) scaler0 add0r.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K H hom_finite_pred Hom_finite hom_finite_closed.
(** Source for [hom_finite_bound]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_bound (f : Hom_finite) : exists N, hom_bounded f N.
Proof. apply/asboolP; exact: hom_finite_proof. Qed.
(** Source for [hom_finite_ext]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_ext (f g : Hom_finite) : f =1 g -> f = g.
Proof. move=> h; apply: val_inj; exact: hom_ext h. Qed.
(** Source for [hom_finite_zeroE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_zeroE x : (0 : Hom_finite) x = 0.
Proof. by []. Qed.
(** Source for [hom_finite_addE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_addE (f g : Hom_finite) x : (f+g) x = f x + g x.
Proof. by []. Qed.
(** Source for [hom_finite_scaleE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_scaleE a (f : Hom_finite) x : (a *: f) x = a *: f x.
Proof. by []. Qed.
(** Source for [hom_finite_sumE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_sumE (I : finType) (f : I -> Hom_finite) x :
  (\sum_i f i) x = \sum_i f i x.
Proof. elim/big_ind2: _ => [|a b c d ha hb|i _]; by rewrite ?hom_finite_zeroE ?hom_finite_addE ?ha ?hb. Qed.

(** Source for [hom_projection]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition hom_projection m (f : Hom V W) : Hom V W :=
  hom_comp f (hom_of_linear (grade G m)).
(** Source for [hom_projectionE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_projectionE m f x : hom_projection m f x = f (grade G m x).
Proof. by []. Qed.
(** Source for [hom_projection_degree]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma hom_projection_degree m (f : Hom V W) : hom_degree G m (hom_projection m f).
Proof.
move=> n x hn hx; rewrite hom_projectionE (grade_homogeneous m hx).
by rewrite eq_sym (negPf hn) linear0.
Qed.
(** Source for [hom_projection_bounded]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma hom_projection_bounded m f : hom_bounded (hom_projection m f) m.+1.
Proof.
move=> n x hn hx; apply: hom_projection_degree hx.
by rewrite neq_ltn hn orbT.
Qed.
(** Source for [finite_hom_grade]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition finite_hom_grade m (f : Hom_finite) : Hom_finite :=
  @FiniteHom (hom_projection m f)
    (introT (asboolP _) (ex_intro _ m.+1 (@hom_projection_bounded m f))).
(** Source for [finite_hom_gradeE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma finite_hom_gradeE m f x : finite_hom_grade m f x = f (grade G m x).
Proof. by []. Qed.
(** Source for [finite_hom_grade_linear]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma finite_hom_grade_linear m : linear (finite_hom_grade m).
Proof.
move=> a f g; apply: hom_finite_ext => x.
by rewrite finite_hom_gradeE !hom_finite_addE !hom_finite_scaleE.
Qed.
HB.instance Definition _ m := GRing.isLinear.Build K Hom_finite Hom_finite
  *:%R (finite_hom_grade m) (finite_hom_grade_linear m).
(** Source for [finite_hom_grade_orthogonal]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma finite_hom_grade_orthogonal m n f :
  finite_hom_grade m (finite_hom_grade n f) = if m == n then finite_hom_grade n f else 0.
Proof.
apply: hom_finite_ext => x; rewrite !finite_hom_gradeE grade_orthogonal.
case hmn: (m == n).
- move/eqP: hmn => ->; by rewrite eqxx finite_hom_gradeE.
- have hnm : (n == m) = false by rewrite eq_sym hmn.
  by rewrite hnm linear0 hom_finite_zeroE.
Qed.
(** Source for [finite_hom_reconstruction]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma finite_hom_reconstruction (f : Hom_finite) N : hom_bounded f N ->
  f = \sum_(i < N) finite_hom_grade i f.
Proof.
move=> hN; apply: hom_finite_ext => x.
elim/(graded_induction (G:=G)): x => [|x y hx hy|n x hx].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite hom_finite_sumE.
  under eq_bigr do rewrite finite_hom_gradeE (grade_homogeneous _ hx).
  under eq_bigr do rewrite (fun_if f) linear0.
  case hn: (n < N)%N.
  + rewrite -big_mkcond; symmetry; exact: (big_pred1 (Ordinal hn)).
  + rewrite (hN n x) //; last by rewrite leqNgt hn.
    symmetry; apply: big1 => i _.
    have hin : ((i : nat) == n) = false.
      apply/negP => /eqP hi; move: (ltn_ord i); by rewrite hi hn.
    by rewrite hin.
Qed.
(** Source for [finite_hom_grade_finite]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma finite_hom_grade_finite f : exists N, f = \sum_(i < N) finite_hom_grade i f.
Proof. have [N hN] := hom_finite_bound f; exists N; exact: finite_hom_reconstruction hN. Qed.
(** Source for [hom_finite_grading]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Definition or construction used to formalise this passage. *)
Definition hom_finite_grading : grading Hom_finite :=
  @Grading K Hom_finite (fun m => GRing.Linear.clone _ _ _ _ (finite_hom_grade m) _)
    finite_hom_grade_orthogonal finite_hom_grade_finite.
(** Source for [hom_finite_gradingE]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma hom_finite_gradingE m f : grade hom_finite_grading m f = finite_hom_grade m f.
Proof. by []. Qed.
End BoundedMaps.
Arguments Hom_finite {K V} W G.
