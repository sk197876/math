(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import DualExterior.
From Federer Require Import DiagonalTensor DiagonalAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, first display: the named commutative algebra
    A = direct_sum_m (A^m V tensor exterior_power W m), realised inside
    the ordinary tensor product of the two full exterior algebras. *)
Section TraceAlgebra.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation GU := (A_star_grading V K^o).
Local Notation GE := (exterior_grading W).
(** Source for [A]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Definition or construction used to formalise
    this passage. *)
Definition A : algebra K := @diagonal_algebra K U E GU GE
  (@alternating_wedge_graded K h2 V K^o (fun x y : K^o => x*y) (scalar_bilinear K))
  (@wedge_graded K W) (coefficient_form_homogeneous V (1 : K^o)) (exterior_unit_homogeneous W).
(** Source for [A_include]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Definition or construction used to formalise
    this passage. *)
Definition A_include : algebra_map A (algebra_tensor U E) :=
  @diagonal_algebra_include K U E GU GE
  (@alternating_wedge_graded K h2 V K^o (fun x y : K^o => x*y) (scalar_bilinear K))
  (@wedge_graded K W) (coefficient_form_homogeneous V (1 : K^o)) (exterior_unit_homogeneous W).
(** Source for [A_commutative]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem A_commutative : commutative (alg_mul A).
Proof.
apply (@diagonal_algebra_commutative K U E GU GE).
- exact (@alternating_wedge_anticommutative K h2 V K^o (fun x y : K^o => x*y) (scalar_bilinear K) (@mulrC K)).
- exact: exterior_anticommutative.
Qed.
(** Source for [A_grading]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Definition or construction used to formalise
    this passage. *)
Definition A_grading : grading A := @diagonal_grading K U E GU GE.
(** Source for [A_pure]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Definition or construction used to formalise
    this passage. *)
Definition A_pure m (phi : A_m V K^o m) (xi : exterior_power W m) : A :=
  @Diagonal K U E GU GE (tensor_inj (form_include phi) (component_val xi))
    (introT (asboolP _) (@diagonal_pure K U E GU GE m (form_include phi) (component_val xi)
      (form_include_homogeneous phi) (component_homogeneous xi))).
(** Source for [A_pureE]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_pureE m phi xi : A_include (@A_pure m phi xi) = tensor_inj (form_include phi) (component_val xi).
Proof. by []. Qed.
(** Source for [A_pure_bilinear]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_pure_bilinear m : bilinear (@A_pure m).
Proof.
split=> [xi c phi psi|phi c xi eta]; apply: val_inj.
- change (tensor_inj (form_include (c *: phi+psi)) (component_val xi) =
    c *: tensor_inj (form_include phi) (component_val xi)+tensor_inj (form_include psi) (component_val xi)).
  by rewrite linearP tensor_inj_addl tensor_inj_scalel.
- change (tensor_inj (form_include phi) (component_val (c *: xi+eta)) =
    c *: tensor_inj (form_include phi) (component_val xi)+tensor_inj (form_include phi) (component_val eta)).
  by rewrite linearP tensor_inj_addr tensor_inj_scaler.
Qed.
(** Source for [A_component]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition A_component m : {linear tensor_space (A_m V K^o m) (exterior_power W m) -> A} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift (@A_pure_bilinear m)) _.
(** Source for [A_componentE]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_componentE m phi xi : A_component m (tensor_inj phi xi) = A_pure phi xi.
Proof. exact: tensor_liftE. Qed.
(** Source for [A_extract]: Federer (1969), 1.4.5, p. 20, opening paragraph,
    displayed diagonal subalgebra A. In words: The direct sum of tensors
    whose two exterior degrees agree is a commutative subalgebra of the
    ordinary tensor product. Definition or construction used to formalise
    this passage. *)
Definition A_extract m : {linear A -> tensor_space (A_m V K^o m) (exterior_power W m)} :=
  linear_comp (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (component GE m) _)) A_include.
(** Source for [A_extract_pure]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_extract_pure m phi xi : A_extract m (@A_pure m phi xi) = tensor_inj phi xi.
Proof.
change (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
  (GRing.Linear.clone _ _ _ _ (component GE m) _) (tensor_inj (form_include phi) (component_val xi)) = tensor_inj phi xi).
by rewrite tensor_mapE /= form_includeK componentK.
Qed.
(** Source for [A_componentK]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma A_componentK m : cancel (A_component m) (A_extract m).
Proof.
apply: tensor_induction => [|x y hx hy|c x hx|phi xi].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space (A_m V K^o m) (exterior_power W m) => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space (A_m V K^o m) (exterior_power W m) => c *: x) hx).
by rewrite A_componentE A_extract_pure.
Qed.
(** Source for [A_component_injective]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem A_component_injective m : injective (A_component m).
Proof. exact (can_inj (@A_componentK m)). Qed.
End TraceAlgebra.
