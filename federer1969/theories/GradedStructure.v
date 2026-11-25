(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  GradedComponents GradedSums GradedUnit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.1: the projections specify an actual internal direct sum.
    Its finite homogeneous decompositions are unique. *)
Section DirectSum.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.

(** Source for [graded_component_decomposition]: Federer (1969), 1.2.1, p.
    11, opening paragraph and degree condition. In words: A graded algebra
    is a vector space with a specified direct sum indexed by nonnegative
    integers and a bilinear multiplication that adds degrees. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem graded_component_decomposition x :
  exists N, x = \sum_(i < N) component_val (component G i x).
Proof. exact: grade_finite. Qed.

(** Source for [grade_homogeneous_sum]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma grade_homogeneous_sum N (u : nat -> V)
    (hu : forall i, homogeneous G i (u i)) (n : 'I_N) :
  grade G n (\sum_(i < N) u i) = u n.
Proof.
rewrite linear_sum /=.
under eq_bigr do rewrite (grade_homogeneous _ (hu _)) eq_sym.
by rewrite -big_mkcond (big_pred1 n).
Qed.

(** Source for [graded_decomposition_unique]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem graded_decomposition_unique N (u : nat -> V)
    (hu : forall i, homogeneous G i (u i)) x :
  x = \sum_(i < N) u i -> forall n : 'I_N, u n = grade G n x.
Proof. by move=> -> n; rewrite grade_homogeneous_sum. Qed.

(** Source for [graded_ext]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem graded_ext x y :
  (forall n, grade G n x = grade G n y) -> x = y.
Proof.
move=> h; have hz n : grade G n (x-y) = 0 by rewrite linearB h subrr.
have [N e] := grade_finite G (x-y).
move: e; under eq_bigr do rewrite hz.
by rewrite big1 // => /subr0_eq.
Qed.
End DirectSum.

Section GradedMap.
Variable K : fieldType.
Variables V W : lmodType K.
Variables (G : grading V) (H : grading W).
Variable f : {linear V -> W}.
Hypothesis hf : preserves_grading G H f.

(** Source for [graded_map_projection]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Theorem graded_map_projection n x : grade H n (f x) = f (grade G n x).
Proof.
have [N ->] := grade_finite G x.
rewrite !linear_sum /=.
apply: eq_bigr => i _.
rewrite (grade_homogeneous n (hf (homogeneous_grade G i x))) grade_orthogonal.
by case: ifP => _; rewrite ?linear0.
Qed.
End GradedMap.

(** The usual extra condition in 1.2.1 is not imposed on every graded
    algebra: the unit is nonzero and spans A_0. Under exactly this condition
    the scalar map is a linear isomorphism onto the actual component A_0. *)
Section ScalarUnit.
Variable K : fieldType.
Variable A : algebra K.
Variable G : grading A.
Hypothesis hm : graded_product G (alg_mul A).

(** Source for [scalar_unit_component]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Definition or construction used to formalise this passage. *)
Definition scalar_unit_component (a : K^o) : graded_component G 0 :=
  component G 0 (a *: alg_one A).
(** Source for [scalar_unit_componentE]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma scalar_unit_componentE a :
  component_val (scalar_unit_component a) = a *: alg_one A.
Proof.
rewrite /scalar_unit_component componentE linearZ /=.
by rewrite (@graded_unit_degree_zero K A G (alg_mul A) (alg_bilinear A)
  hm (alg_one A) (@alg_unitl K A) (@alg_unitr K A)).
Qed.
(** Source for [scalar_unit_component_linear]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_component_linear : linear scalar_unit_component.
Proof.
move=> a b c; apply/val_inj.
change (component_val (scalar_unit_component (a *: b + c)) =
  component_val (a *: scalar_unit_component b + scalar_unit_component c)).
rewrite linearD linearZ.
change (component_val (scalar_unit_component (a *: b + c)) =
  a *: component_val (scalar_unit_component b) + component_val (scalar_unit_component c)).
rewrite !scalar_unit_componentE.
by rewrite scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o (graded_component G 0)
  *:%R scalar_unit_component scalar_unit_component_linear.

(** Source for [scalar_unit_grading]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Definition or construction used to formalise this passage. *)
Definition scalar_unit_grading : Prop :=
  alg_one A != 0 /\
  forall x, homogeneous G 0 x -> exists a : K, x = a *: alg_one A.

Hypothesis hu : scalar_unit_grading.
(** Source for [scalar_unit_component_injective]: Federer (1969), 1.2.1, p.
    11, paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_component_injective : injective scalar_unit_component.
Proof.
move=> a b e; have h := congr1 component_val e.
rewrite !scalar_unit_componentE in h.
have hz : (a-b) *: alg_one A = 0 by rewrite scalerBl h subrr.
move/eqP: hz; rewrite scaler_eq0 (negPf (proj1 hu)) orbF subr_eq0 => /eqP.
by [].
Qed.
(** Source for [scalar_unit_preimage]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_preimage (x : graded_component G 0) :
  exists a : K^o, scalar_unit_component a == x.
Proof.
have [a ha] := (proj2 hu) _ (component_homogeneous x).
exists a; apply/eqP; apply/val_inj.
change (component_val (scalar_unit_component a) = component_val x).
by rewrite scalar_unit_componentE -ha.
Qed.
(** Source for [scalar_unit_inverse]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Definition or construction used to formalise this passage. *)
Definition scalar_unit_inverse x := xchoose (scalar_unit_preimage x).
(** Source for [scalar_unit_inverseK]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_inverseK : cancel scalar_unit_inverse scalar_unit_component.
Proof. by move=> x; apply/eqP; exact: (xchooseP (scalar_unit_preimage x)). Qed.
(** Source for [scalar_unit_componentK]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_componentK : cancel scalar_unit_component scalar_unit_inverse.
Proof. by move=> a; apply: scalar_unit_component_injective; rewrite scalar_unit_inverseK. Qed.
(** Source for [scalar_unit_inverse_linear]: Federer (1969), 1.2.1, p. 11,
    paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma scalar_unit_inverse_linear : linear scalar_unit_inverse.
Proof.
move=> a x y; apply: scalar_unit_component_injective.
by rewrite scalar_unit_component_linear !scalar_unit_inverseK.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (graded_component G 0) K^o
  *:%R scalar_unit_inverse scalar_unit_inverse_linear.
(** Source for [scalar_unit_component_isomorphism]: Federer (1969), 1.2.1,
    p. 11, paragraph beginning Usually. In words: Associativity and a scalar
    identification of degree zero taking one to the unit are usual
    additional conditions, not part of the preceding general definition.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem scalar_unit_component_isomorphism :
  exists g : {linear graded_component G 0 -> K^o},
    cancel scalar_unit_component g /\ cancel g scalar_unit_component.
Proof.
exists (GRing.Linear.clone _ _ _ _ scalar_unit_inverse _).
split; [exact: scalar_unit_componentK | exact: scalar_unit_inverseK].
Qed.
End ScalarUnit.
