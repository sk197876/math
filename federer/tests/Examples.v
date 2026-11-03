(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector TensorProduct TensorMaps TensorSpan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** A non-degeneracy example in free spaces on arbitrary index types.
    Taking A = B = nat gives an example with infinitely many basis vectors. *)
Section Coordinates.
Variable K : fieldType.
Variables A B : choiceType.
Variables (i : A) (j : B).
Local Notation FA := (GRing.Lmodule.clone K (free_vector K A) _).
Local Notation FB := (GRing.Lmodule.clone K (free_vector K B) _).

(** Source for [coordinate_pairing]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition coordinate_pairing (u : free_vector K A) (v : free_vector K B) : K^o :=
  u i * v j.

(** Source for [coordinate_pairing_bilinear]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma coordinate_pairing_bilinear : bilinear coordinate_pairing.
Proof.
split.
  move=> v a u u'; rewrite /coordinate_pairing free_addE free_scaleE.
  by rewrite mulrDl /GRing.scale /= mulrA.
move=> u a v v'; rewrite /coordinate_pairing free_addE free_scaleE.
by rewrite mulrDr /GRing.scale /= mulrCA.
Qed.

(** Source for [tensor_coordinate]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition tensor_coordinate :
    {linear tensor_space FA FB -> K^o} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift coordinate_pairing_bilinear) _.

(** Source for [tensor_coordinateE]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma tensor_coordinateE u v :
  tensor_coordinate (tensor_inj u v) = u i * v j.
Proof. exact: tensor_liftE. Qed.

(** Source for [tensor_coordinate_delta]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma tensor_coordinate_delta :
  tensor_coordinate (tensor_inj (delta K i) (delta K j)) = 1.
Proof. by rewrite tensor_coordinateE !deltaE !eqxx mulr1. Qed.

(** Source for [pure_delta_nonzero]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Theorem pure_delta_nonzero : tensor_inj (delta K i) (delta K j) != 0.
Proof.
apply/eqP=> h.
have e := tensor_coordinate_delta.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End Coordinates.

Section InfiniteIndexExample.
Variable K : fieldType.
Local Notation FN :=
  (GRing.Lmodule.clone K (free_vector K (Choice.clone nat _)) _).

(** Source for [nat_basis_tensor_nonzero]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Example nat_basis_tensor_nonzero (m n : nat) :
  tensor_inj (delta K m) (delta K n) != 0.
Proof. exact: pure_delta_nonzero. Qed.

(** Source for [swap_back]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Local regression example for this passage; the example itself is not
    stated in the book. *)
Example swap_back (t : tensor_space FN FN) :
  tensor_swap _ _ (tensor_swap _ _ t) = t.
Proof. exact: tensor_swapK. Qed.
End InfiniteIndexExample.

From mathcomp Require Import all_algebra.
From Federer Require Import TensorFamily TensorFamilyCanonical LinearBasis
  FiniteDimension.

Section TensorFamilyBoundaryExamples.
Variable K : fieldType.

(** Source for [tensor_empty_family_dimension_regression]: Federer 1.1.2,
    p. 10, product dimension formula; regression at zero factors, where
    the tensor product has dimension one rather than zero. *)
Example tensor_empty_family_dimension_regression
    (V : 'I_0 -> lmodType K) (J : 'I_0 -> finType)
    (e : forall i, J i -> V i) (he : forall i, is_basis (@e i)) :
  dim (@tensor_family_finite_space K 0 V J e he (tensor_family V)
    (tensor_family_mul V) (tensor_familyP V)) = 1%N.
Proof. by rewrite tensor_family_dimension /image_mem enum_ord0. Qed.

Local Notation ZI := (Choice.clone 'I_0 _).
Local Notation ZV := (GRing.Lmodule.clone K (free_vector K ZI) _).
Local Notation VZ := (fun _ : 'I_1 => ZV).
Local Notation JZ := (fun _ : 'I_1 => Finite.clone 'I_0 _).

(** Source for [tensor_zero_factor_basis_regression]: Federer 1.1.2,
    p. 10; the actual zero factor's empty basis, used in the next test. *)
Lemma tensor_zero_factor_basis_regression (i : 'I_1) :
  is_basis (fun j : JZ i => delta K j : VZ i).
Proof. exact: free_basis. Qed.

(** Source for [tensor_zero_factor_dimension_regression]: Federer 1.1.2,
    p. 10, dimension product; a genuine empty basis gives dimension zero. *)
Example tensor_zero_factor_dimension_regression :
  dim (@tensor_family_finite_space K 1 VZ JZ
    (fun _ j => delta K j) tensor_zero_factor_basis_regression
    (tensor_family VZ) (tensor_family_mul VZ) (tensor_familyP VZ)) = 0%N.
Proof. by rewrite tensor_family_dimension /image_mem enum_ordSl enum_ord0 /= ?card_ord. Qed.

Local Notation NI := (Choice.clone nat _).
Local Notation NV := (GRing.Lmodule.clone K (free_vector K NI) _).
Local Notation VN := (fun _ : 'I_1 => NV).
Local Notation JN := (fun _ : 'I_1 => NI).

(** Source for [tensor_infinite_factor_basis_regression]: Federer 1.1.2,
    p. 10; an infinite basis is permitted without a finite-factor premise. *)
Lemma tensor_infinite_factor_basis_regression (i : 'I_1) :
  is_basis (fun j : JN i => delta K j : VN i).
Proof. exact: free_basis. Qed.

(** Source for [tensor_infinite_basis_nonzero_regression]: Federer 1.1.2,
    p. 10; each actual natural-indexed basis product is nonzero, testing
    the arbitrary-dimensional result on a concrete infinite factor. *)
Example tensor_infinite_basis_nonzero_regression n :
  @tensor_family_basis K 1 VN JN (fun _ j => delta K j)
    (tensor_family VN) (tensor_family_mul VN) [ffun _ => n] <> 0.
Proof.
pose b : {dffun forall i, JN i} := [ffun _ => n].
pose c := @tensor_basis_coordinate K 1 VN JN (fun _ j => delta K j)
  tensor_infinite_factor_basis_regression (tensor_family VN)
  (tensor_family_mul VN) (tensor_familyP VN) b.
have hc : c (@tensor_family_basis K 1 VN JN (fun _ j => delta K j)
    (tensor_family VN) (tensor_family_mul VN) b) = 1.
  by rewrite /c /tensor_basis_coordinate /tensor_family_basis
    abstract_tensor_family_liftE tensor_basis_delta_product eqxx.
move=> hz; rewrite hz linear0 in hc.
by move: hc; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End TensorFamilyBoundaryExamples.

From Federer Require Import Hom HomTensor HomTensorGeneral HomTensorInfinite
  CoefficientCoordinates FiniteCoordinates.

Section HomTensorGeneralExamples.
Variable K : fieldType.
Local Notation NI := (Choice.clone nat _).
Local Notation FV := (GRing.Lmodule.clone K (free_vector K NI) _).

(** Source for [infinite_source_coordinate_map]: Federer 1.1.4, p. 11;
    regression data: an actual nonzero map from the infinite free vector
    space to a one-dimensional target, using one coordinate functional. *)
Definition infinite_source_coordinate_map n : Hom FV (coordinate_space K 1) :=
  hom_with_coefficient (@coordinate_basis K 1 ord0)
    (hom_of_linear (GRing.Linear.clone _ _ _ _ (@free_eval K NI n) _)).

(** Source for [tensor_Hom_infinite_source_inverse_regression]: Federer
    1.1.4, p. 11, finite-target surjectivity; its actual inverse recovers a
    nonzero coordinate map on an infinite-dimensional source. *)
Example tensor_Hom_infinite_source_inverse_regression n :
  @tensor_Hom K FV (coordinate_space K 1)
    (Hom_tensor_finite_target (@coordinate_basisP K 1)
      (infinite_source_coordinate_map n)) (delta K n) =
    @coordinate_basis K 1 ord0.
Proof.
rewrite Hom_tensor_finite_targetK /infinite_source_coordinate_map
  hom_with_coefficientE hom_of_linearE.
change ((@delta K NI n) n *: @coordinate_basis K 1 ord0 = @coordinate_basis K 1 ord0).
by rewrite deltaE eqxx scale1r.
Qed.

(** Source for [tensor_Hom_zero_target_regression]: Federer 1.1.4,
    p. 11, unrestricted injectivity; a zero target annihilates the entire
    tensor even though the original source is infinite-dimensional. *)
Example tensor_Hom_zero_target_regression
    (t : tensor_space (Hom FV K^o) (coordinate_space K 0)) : t = 0.
Proof.
apply: (@tensor_Hom_zero_fibre K FV (coordinate_space K 0) t).
apply: hom_ext=> v; rewrite hom_zeroE; exact: coordinate_zero.
Qed.

(** Source for [tensor_Hom_both_infinite_regression]: Federer 1.1.4,
    p. 11, the actual defining evaluation of Phi; both vector spaces have
    natural-indexed infinite bases and the displayed value is a basis vector. *)
Example tensor_Hom_both_infinite_regression m n :
  @tensor_Hom K FV FV
    (tensor_inj (hom_of_linear (GRing.Linear.clone _ _ _ _ (@free_eval K NI m) _))
      (delta K n)) (delta K m) = delta K n.
Proof.
rewrite tensor_HomE hom_of_linearE.
change ((@delta K NI m) m *: delta K n = delta K n).
by rewrite deltaE eqxx scale1r.
Qed.

(** Source for [tensor_Hom_identity_missing_regression]: Federer 1.1.4,
    p. 11, simultaneous-infinite exception. The actual identity of the
    natural-indexed free space has no tensor preimage, although every
    individual basis vector is a value of a pure tensor map. *)
Example tensor_Hom_identity_missing_regression :
  ~ exists t, @tensor_Hom K FV FV t = hom_of_linear (linear_id FV).
Proof.
move=> [t ht].
have [S hS] := tensor_Hom_finite_coordinate_support (linear_id FV) t.
have [j hj] := tensor_coordinate_fresh_index S.
have h := hS (delta K j) j hj.
change ((@tensor_Hom K FV FV t (delta K j)) j = 0) in h.
rewrite ht hom_of_linearE in h.
change ((@delta K NI j) j = 0) in h.
rewrite deltaE eqxx in h.
by move: h; apply/eqP; rewrite oner_eq0.
Qed.
End HomTensorGeneralExamples.
