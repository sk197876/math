(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import DiagonalTensor DiagonalAlgebra TraceAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, first display: identify the actual homogeneous
    summands of A with A^m V tensor exterior_power W m. *)
Section TraceComponents.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).
Local Notation D := (A h2 V W).
Local Notation G := (A_grading h2 V W).
Local Notation include := (@A_include K h2 V W).
(** Source for [A_include_injective]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_include_injective : injective include.
Proof. exact: val_inj. Qed.
(** Source for [A_component_include]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_component_include m t : include (@A_component K h2 V W m t) =
  tensor_map (GRing.Linear.clone _ _ _ _ (@form_include K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (@component_val K (exterior_space W) (exterior_grading W) m) _) t.
Proof.
elim/tensor_induction: t => [|x y hx hy|c x hx|phi xi].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : T => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : T => c *: x) hx).
by rewrite A_componentE A_pureE tensor_mapE.
Qed.
(** Source for [A_projection_factorisation]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma A_projection_factorisation m t :
  tensor_map (GRing.Linear.clone _ _ _ _ (@form_include K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (@component_val K (exterior_space W) (exterior_grading W) m) _)
    (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
      (GRing.Linear.clone _ _ _ _ (component (exterior_grading W) m) _) t) =
  @diagonal_projection K U E (A_star_grading V K^o) (exterior_grading W) m t.
Proof.
pose f : {linear T -> T} := linear_comp
  (tensor_map (GRing.Linear.clone _ _ _ _ (@form_include K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (@component_val K (exterior_space W) (exterior_grading W) m) _))
  (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (component (exterior_grading W) m) _)).
change (f t = @diagonal_projection K U E (A_star_grading V K^o) (exterior_grading W) m t).
apply: (tensor_ext (tensor_exists U E) f
  (@diagonal_projection K U E (A_star_grading V K^o) (exterior_grading W) m)) t => phi xi.
change (tensor_map (GRing.Linear.clone _ _ _ _ (@form_include K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (@component_val K (exterior_space W) (exterior_grading W) m) _)
    (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
      (GRing.Linear.clone _ _ _ _ (component (exterior_grading W) m) _) (tensor_inj phi xi)) =
  @diagonal_projection K U E (A_star_grading V K^o) (exterior_grading W) m (tensor_inj phi xi)).
by rewrite /diagonal_projection !tensor_mapE /= form_componentK.
Qed.
(** Source for [A_component_extract]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem A_component_extract m x : @A_component K h2 V W m (@A_extract K h2 V W m x) = grade G m x.
Proof.
apply A_include_injective; rewrite A_component_include.
change (tensor_map (GRing.Linear.clone _ _ _ _ (@form_include K V K^o m) _)
    (GRing.Linear.clone _ _ _ _ (@component_val K (exterior_space W) (exterior_grading W) m) _)
    (tensor_map (GRing.Linear.clone _ _ _ _ (@form_component K V K^o m) _)
      (GRing.Linear.clone _ _ _ _ (component (exterior_grading W) m) _) (include x)) =
  @diagonal_projection K U E (A_star_grading V K^o) (exterior_grading W) m (include x)).
exact: A_projection_factorisation.
Qed.
(** Source for [A_component_homogeneous]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma A_component_homogeneous m t : homogeneous G m (@A_component K h2 V W m t).
Proof. by rewrite /homogeneous -A_component_extract A_componentK. Qed.
(** Source for [A_component_image]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem A_component_image m x : homogeneous G m x <->
  exists t, @A_component K h2 V W m t = x.
Proof.
split.
- move=> hx; exists (@A_extract K h2 V W m x); by rewrite A_component_extract hx.
- move=> [t <-]; exact: A_component_homogeneous.
Qed.
(** Source for [A_direct_sum]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem A_direct_sum x : exists N,
  x = \sum_(i < N) @A_component K h2 V W i (@A_extract K h2 V W i x).
Proof.
have [N hN] := grade_finite G x; exists N.
by under eq_bigr do rewrite A_component_extract.
Qed.
End TraceComponents.
