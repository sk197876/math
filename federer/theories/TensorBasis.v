(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import Graded.
From Federer Require Import LinearBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.2, used in 1.3.2: tensor products of basis vectors form a
    basis. Index sets may be infinite; coordinates always have finite support. *)
Section TensorBasis.
Variable K : fieldType.
Variables I J : choiceType.
Variables V W : lmodType K.
Variables (e : I -> V) (d : J -> W).
Hypotheses (he : is_basis e) (hd : is_basis d).
Local Notation IJ := (Choice.clone (I * J)%type _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K IJ) _).
Local Notation T := (tensor_space V W).

(** Source for [tensor_basis]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Definition or construction used to formalise this passage. *)
Definition tensor_basis (ij : IJ) : T := tensor_inj (e ij.1) (d ij.2).
(** Source for [tensor_coordinates_fun]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition tensor_coordinates_fun v w : F :=
  free_bilinear (fun i j => delta K (i,j)) (basis_coordinates he v) (basis_coordinates hd w).
(** Source for [tensor_coordinates_fun_bilinear]: Federer (1969), 1.1.2, p.
    10, final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_coordinates_fun_bilinear : bilinear tensor_coordinates_fun.
Proof.
exact: bilinear_pre (basis_coordinates he) (basis_coordinates hd)
  (free_bilinear_bilinear (fun i j => delta K (i,j))).
Qed.
(** Source for [tensor_basis_coordinates]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition tensor_basis_coordinates : {linear T -> F} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift tensor_coordinates_fun_bilinear) _.
(** Source for [tensor_basis_coordinatesE]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_basis_coordinatesE v w :
  tensor_basis_coordinates (tensor_inj v w) = tensor_coordinates_fun v w.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_basis_coordinates_generators]: Federer (1969), 1.1.2,
    p. 10, final paragraph and dimension formula. In words: Pure tensors
    formed from bases of the factors form a basis of the tensor product;
    finite dimensions multiply. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_basis_coordinates_generators i j :
  tensor_basis_coordinates (tensor_inj (e i) (d j)) = delta K (i,j).
Proof.
by rewrite tensor_basis_coordinatesE /tensor_coordinates_fun !basis_coordinatesE free_bilinearE.
Qed.

(** Source for [tensor_basis_synthesisK]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_basis_synthesisK : cancel (basis_synthesis tensor_basis) tensor_basis_coordinates.
Proof.
apply: (free_linear_ext (linear_comp tensor_basis_coordinates (basis_synthesis tensor_basis))
  (linear_id F)) => [[i j]].
change (tensor_basis_coordinates (basis_synthesis tensor_basis (delta K (i,j))) = delta K (i,j)).
by rewrite basis_synthesisE tensor_basis_coordinates_generators.
Qed.
(** Source for [tensor_basis_coordinatesK]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_basis_coordinatesK : cancel tensor_basis_coordinates (basis_synthesis tensor_basis).
Proof.
apply: (tensor_ext (tensor_exists V W)
  (linear_comp (basis_synthesis tensor_basis) tensor_basis_coordinates) (linear_id T)).
change (forall v w, basis_synthesis tensor_basis
  (tensor_basis_coordinates (tensor_inj v w)) = tensor_inj v w).
apply: (basis_induction he) => [w|v v' hv hv' w|a v hv w|i].
- by rewrite tensor_inj0l !linear0.
- by rewrite tensor_inj_addl !linearD hv hv'.
- by rewrite tensor_inj_scalel !linearZ hv.
apply: (basis_induction hd) => [|w w' hw hw'|a w hw|j].
- by rewrite tensor_inj0r !linear0.
- by rewrite tensor_inj_addr !linearD hw hw'.
- by rewrite tensor_inj_scaler !linearZ hw.
by rewrite tensor_basis_coordinates_generators basis_synthesisE.
Qed.

(** Source for [tensor_basisP]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem tensor_basisP : is_basis tensor_basis.
Proof. exists tensor_basis_coordinates; split; [exact: tensor_basis_synthesisK | exact: tensor_basis_coordinatesK]. Qed.
End TensorBasis.

Section GradedTensorBasis.
Variable K : fieldType.
Variables I J : choiceType.
Variables V W : lmodType K.
Variables (G : grading V) (H : grading W).
Variables (e : I -> V) (d : J -> W) (p : I -> nat) (q : J -> nat).
Hypotheses (he : is_graded_basis G e p) (hd : is_graded_basis H d q).

(** Source for [graded_tensor_basisP]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem graded_tensor_basisP : is_graded_basis (tensor_grading_product G H)
  (tensor_basis e d) (fun ij => (p ij.1 + q ij.2)%N).
Proof.
have [hbe hge] := he; have [hbd hgd] := hd; split.
  exact: tensor_basisP hbe hbd.
by move=> [i j]; exact: tensor_homogeneous_pure (hge i) (hgd j).
Qed.
End GradedTensorBasis.
