(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import TensorUP FreeVector Bilinear ExteriorCore.
From Federer Require Import LinearBasis ExteriorIndices FiniteExteriorPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Federer 1.3.2, dimension assertion: a finite basis supplies the actual
    finite-dimensional structure on its vector space. The adapter below
    uses MathComp's abstract vector-space interface; its dimension is the
    cardinality of the given basis. *)
Section TransportDimension.
Variable K : fieldType.
Variables V W : lmodType K.
Variables (f : {linear V -> W}) (g : {linear W -> V}).
Hypotheses (fg : cancel f g) (gf : cancel g f).
(** Source for [transport_vector_axiom]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma transport_vector_axiom n : Vector.axiom n W -> Vector.axiom n V.
Proof.
move=> [j hj hbij]; exists (fun x => j (f x)).
- by move=> a x y; rewrite linearP hj.
- case: hbij => k jk kj.
  exists (fun r => g (k r)); [by move=> x; rewrite jk fg | by move=> r; rewrite gf kj].
Qed.
End TransportDimension.

Section FiniteBasisDimension.
Variable K : fieldType.
Variable I : finType.
Variable V : lmodType K.
Variable e : I -> V.
Hypothesis he : is_basis e.
Local Notation F := (GRing.Lmodule.clone K (free_vector K (Choice.clone I _)) _).
Local Notation C := (GRing.Lmodule.clone K {ffun I -> K^o} _).

(** Source for [finite_coefficients]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_coefficients (x : F) : C := [ffun i => x i].
(** Source for [finite_coefficients_linear]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_coefficients_linear : linear finite_coefficients.
Proof.
move=> a x y; apply/ffunP=> i.
by rewrite /finite_coefficients !ffunE free_addE free_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K F C *:%R
  finite_coefficients finite_coefficients_linear.
(** Source for [finite_coefficients_inverse]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_coefficients_inverse (x : C) : F := [fsfun i in [fset j | j : I] => x i | 0].
(** Source for [finite_coefficients_inverseE]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_coefficients_inverseE (x : C) i : finite_coefficients_inverse x i = x i.
Proof. by rewrite /finite_coefficients_inverse fsfunE inE. Qed.
(** Source for [finite_coefficients_inverse_linear]: Federer (1969), 1.3.2,
    pp. 14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_coefficients_inverse_linear : linear finite_coefficients_inverse.
Proof.
move=> a x y; apply/fsfunP=> i.
by rewrite finite_coefficients_inverseE free_addE free_scaleE !finite_coefficients_inverseE !ffunE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K C F *:%R
  finite_coefficients_inverse finite_coefficients_inverse_linear.
(** Source for [finite_coefficientsK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_coefficientsK : cancel finite_coefficients finite_coefficients_inverse.
Proof. by move=> x; apply/fsfunP=> i; rewrite finite_coefficients_inverseE /finite_coefficients ffunE. Qed.
(** Source for [finite_coefficients_inverseK]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_coefficients_inverseK : cancel finite_coefficients_inverse finite_coefficients.
Proof. by move=> x; apply/ffunP=> i; rewrite /finite_coefficients ffunE finite_coefficients_inverseE. Qed.

(** Source for [finite_basis_coordinates]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_basis_coordinates : {linear V -> C} :=
  linear_comp (GRing.Linear.clone _ _ _ _ finite_coefficients _) (basis_coordinates he).
(** Source for [finite_basis_synthesis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_basis_synthesis : {linear C -> V} :=
  linear_comp (basis_synthesis e) (GRing.Linear.clone _ _ _ _ finite_coefficients_inverse _).
(** Source for [finite_basis_coordinatesK]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_basis_coordinatesK : cancel finite_basis_coordinates finite_basis_synthesis.
Proof.
move=> x; change (basis_synthesis e
  (finite_coefficients_inverse (finite_coefficients (basis_coordinates he x))) = x).
by rewrite finite_coefficientsK basis_coordinatesK.
Qed.
(** Source for [finite_basis_synthesisK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_basis_synthesisK : cancel finite_basis_synthesis finite_basis_coordinates.
Proof.
move=> x; change (finite_coefficients (basis_coordinates he
  (basis_synthesis e (finite_coefficients_inverse x))) = x).
by rewrite basis_synthesisK finite_coefficients_inverseK.
Qed.
(** Source for [finite_basis_vector_axiom]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_basis_vector_axiom : Vector.axiom #|I| V.
Proof.
apply: (transport_vector_axiom finite_basis_coordinatesK finite_basis_synthesisK).
have h := @ffun_vect_iso I K (Vector.clone K K^o _).
rewrite muln1 in h; case: h => f [fZ fD] fbij.
by exists f => // a u v; rewrite fD fZ.
Qed.
(** Source for [finite_basis_space]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_basis_space : Type := let _ := he in V.
HB.instance Definition _ := GRing.Lmodule.copy finite_basis_space V.
HB.instance Definition _ := Lmodule_hasFinDim.Build K finite_basis_space finite_basis_vector_axiom.
(** Source for [finite_basis_vect]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_basis_vect : vectType K := Vector.clone K finite_basis_space _.
(** Source for [finite_basis_dimension]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_basis_dimension : dim finite_basis_vect = #|I|.
Proof. by []. Qed.
End FiniteBasisDimension.

(** Federer 1.3.2, final paragraph: dim wedge^m V = binomial(n,m).
    This also holds for m>n; the stronger zero-space assertion is proved
    separately as exterior_power_above_dimension. *)
Section ExteriorDimension.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
(** Source for [finite_exterior_power]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_exterior_power m : vectType K :=
  finite_basis_vect (finite_e_lambda_basis he h2 m).
(** Source for [exterior_power_dimension]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem exterior_power_dimension m : dim (finite_exterior_power m) = 'C(n,m).
Proof. rewrite /finite_exterior_power finite_basis_dimension; exact: card_Lambda. Qed.
End ExteriorDimension.
