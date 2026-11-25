(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, unit assertion: the degree-zero coefficient acts as a
    unit because augmentation is a counit for Psi. We obtain its two
    contractions as algebra maps using the maps of 1.3.1 and Phi. *)
Section Counit.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation T := (unital_graded_tensor E E true).
(** Source for [vector_zero]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition vector_zero : {linear V -> V} := hom_as_linear (0 : Hom V V).
(** Source for [exterior_zero_map]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition exterior_zero_map := exterior_algebra_map vector_zero.
(** Source for [exterior_zero_mapE]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_zero_mapE x : exterior_zero_map x = exterior_scalar V (exterior_augmentation V x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- rewrite /exterior_zero_map exterior_algebra_map_word exterior_augmentation_word.
  case: s => [|v s].
  + by rewrite /word_degree_zero /exterior_scalar /= scale1r.
  + rewrite map_cons exterior_word_cons.
    change (wedge (exterior_generator (0 : V)) (exterior_word [seq vector_zero v | v <- s]) =
      (0 : K) *: exterior_unit V).
    by rewrite linear0 (bil0l (wedge_bilinear V)) scale0r.
Qed.
Local Notation F := (exterior_algebra_map vector_zero).
Local Notation hf := (@exterior_algebra_map_graded K V V vector_zero).
Local Notation idE := (algebra_id E).
Local Notation P := (@Phi K E (@exterior_anticommutative K V)).
(** Source for [counit_left]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition counit_left : algebra_map T E :=
  algebra_comp P (@unital_tensor_map K E E E E F idE hf (fun n x hx => hx) true).
(** Source for [counit_right]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition counit_right : algebra_map T E :=
  algebra_comp P (@unital_tensor_map K E E E E idE F (fun n x hx => hx) hf true).
(** Source for [counit_leftE]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma counit_leftE a b : counit_left (tensor_inj a b) = (exterior_augmentation V a : K) *: b.
Proof.
change (P (tensor_map F idE (tensor_inj a b)) = (exterior_augmentation V a : K) *: b).
rewrite tensor_mapE PhiE.
change (wedge (exterior_zero_map a) b = (exterior_augmentation V a : K) *: b).
by rewrite exterior_zero_mapE /exterior_scalar (bilZl (wedge_bilinear V)) wedge_unitl.
Qed.
(** Source for [counit_rightE]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma counit_rightE a b : counit_right (tensor_inj a b) = (exterior_augmentation V b : K) *: a.
Proof.
change (P (tensor_map idE F (tensor_inj a b)) = (exterior_augmentation V b : K) *: a).
rewrite tensor_mapE PhiE.
change (wedge a (exterior_zero_map b) = (exterior_augmentation V b : K) *: a).
by rewrite exterior_zero_mapE /exterior_scalar (bilZr (wedge_bilinear V)) wedge_unitr.
Qed.
Variable h2 : (1+1 : K) != 0.
(** Source for [counit_left_Psi]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma counit_left_Psi x : counit_left (Psi h2 V x) = x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp counit_left (Psi h2 V)) idE) x => v.
change (counit_left (Psi h2 V (exterior_generator v)) = exterior_generator v).
have h0 : exterior_augmentation V (exterior_generator v) = 0 := exterior_augmentation_word [::v].
have hl := @counit_leftE (exterior_generator v) (exterior_unit V).
rewrite h0 scale0r in hl.
have hr := @counit_leftE (exterior_unit V) (exterior_generator v).
rewrite exterior_augmentation_unit scale1r in hr.
apply: eq_trans (congr1 counit_left (@PsiE K h2 V v)) _.
apply: eq_trans (linD (linearP counit_left) _ _) _.
exact (eq_trans (congr2 +%R hl hr) (add0r _)).
Qed.
(** Source for [counit_right_Psi]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma counit_right_Psi x : counit_right (Psi h2 V x) = x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp counit_right (Psi h2 V)) idE) x => v.
change (counit_right (Psi h2 V (exterior_generator v)) = exterior_generator v).
have h0 : exterior_augmentation V (exterior_generator v) = 0 := exterior_augmentation_word [::v].
have hl := @counit_rightE (exterior_generator v) (exterior_unit V).
rewrite exterior_augmentation_unit scale1r in hl.
have hr := @counit_rightE (exterior_unit V) (exterior_generator v).
rewrite h0 scale0r in hr.
apply: eq_trans (congr1 counit_right (@PsiE K h2 V v)) _.
apply: eq_trans (linD (linearP counit_right) _ _) _.
exact (eq_trans (congr2 +%R hl hr) (addr0 _)).
Qed.
End Counit.
