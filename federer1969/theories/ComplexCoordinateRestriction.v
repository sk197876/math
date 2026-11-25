(** Federer (1969), 1.6.6, p. 27, basis of complex-valued real forms. This
    supporting comparison extends a real basis to complex coordinates and
    restricts complex alternating forms along the coordinate embedding. It
    constructs the comparison rather than assuming a complexification or a
    mixed-form basis. Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingDual CovectorProducts
  ScalarRestriction ComplexAlternatingForms ComplexValuedForms FormBasisValues
  FiniteCoordinates FiniteDualDimension FiniteExteriorPowers BasisMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Coordinates.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Hypothesis hR : (1+1 : R) != 0.
Hypothesis hC : (1+1 : C) != 0.
Variable U : lmodType R.
Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.
Local Notation E := (coordinate_space C n).
Local Notation ER := (restricted_space embed E).
Local Notation eb := (@coordinate_basis C n).

(** Source for [extended_coordinates]: Federer 1.6.6, p. 27,
    complex basis of real forms. Supporting real-linear embedding in
    the complex coordinate space belonging to the given real basis. *)
Definition extended_coordinates (v : U) : ER :=
  [ffun j => embed (dual_basis he j v)].

(** Source for [extended_coordinates_linear]: Federer 1.6.6,
    p. 27, complex basis of real forms. Supporting real linearity of
    the coordinate embedding. *)
Lemma extended_coordinates_linear : linear extended_coordinates.
Proof.
move=> a x y; apply/ffunP => j.
rewrite /extended_coordinates !ffunE.
change (embed (dual_basis he j (a *: x + y)) =
  embed a * embed (dual_basis he j x) + embed (dual_basis he j y)).
rewrite linearP.
change (embed (a * dual_basis he j x + dual_basis he j y) =
  embed a * embed (dual_basis he j x) + embed (dual_basis he j y)).
by rewrite rmorphD rmorphM.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R U ER *:%R
  extended_coordinates extended_coordinates_linear.

(** Source for [extended_coordinates_map]: Federer 1.6.6,
    p. 27, complex basis of real forms. The coordinate embedding
    packaged with its proved real linearity. *)
Definition extended_coordinates_map : {linear U -> ER} :=
  GRing.Linear.clone _ _ _ _ extended_coordinates _.

(** Source for [extended_coordinates_basis]: Federer 1.6.6,
    p. 27, complex basis of real forms. The given real basis maps
    to the standard complex coordinate basis. *)
Lemma extended_coordinates_basis j : extended_coordinates (e j) = eb j.
Proof.
apply/ffunP=> i; rewrite /extended_coordinates /coordinate_basis !ffunE dual_basisE.
rewrite (eq_sym i j).
by case: (j == i); rewrite ?rmorph1 ?rmorph0.
Qed.

(** Source for [coordinate_form_restriction]: Federer 1.6.6,
    p. 27, complex basis of real forms. Restriction of a complex
    alternating coordinate form along the real coordinate embedding. *)
Definition coordinate_form_restriction m (a : A_m E C^o m) :
    complex_valued_form embed U C^o m :=
  real_as_complex_valued (A_m_dual extended_coordinates_map (restrict_form embed a)).

(** Source for [coordinate_form_restrictionE]: Federer 1.6.6,
    p. 27, complex basis of real forms. Restriction is composition
    on each vector argument. *)
Lemma coordinate_form_restrictionE m (a : A_m E C^o m) t :
  coordinate_form_restriction a t = a (map_tuple extended_coordinates t).
Proof.
change (A_m_dual extended_coordinates_map (restrict_form embed a) t =
  a (map_tuple extended_coordinates t)).
by rewrite A_m_dualE.
Qed.

(** Source for [coordinate_form_restriction_linear]: Federer
    1.6.6, p. 27, complex basis of real forms. The comparison is C-linear. *)
Lemma coordinate_form_restriction_linear m : linear (@coordinate_form_restriction m).
Proof.
move=> c a b; apply: complex_valued_form_ext => t.
rewrite [LHS]coordinate_form_restrictionE.
change ((c *: a + b) (map_tuple extended_coordinates t) =
  c * coordinate_form_restriction a t + coordinate_form_restriction b t).
by rewrite form_addE form_scaleE !coordinate_form_restrictionE.
Qed.
HB.instance Definition _ m := GRing.isLinear.Build C (A_m E C^o m)
  (complex_valued_form embed U C^o m) *:%R
  (@coordinate_form_restriction m) (@coordinate_form_restriction_linear m).

(** Source for [coordinate_restriction_basis_values]: Federer
    1.6.6, p. 27, complex basis of real forms. Restriction preserves
    all increasing basis-tuple coordinates. *)
Lemma coordinate_restriction_basis_values m (a : A_m E C^o m) (l : Lambda n m) :
  coordinate_form_restriction a [tuple of map e (val l)] =
  a [tuple of map eb (val l)].
Proof.
rewrite coordinate_form_restrictionE; congr (a _); apply: val_inj.
change (map extended_coordinates (map e (val l)) = map eb (val l)).
rewrite -map_comp; apply: eq_map=> j; exact: extended_coordinates_basis.
Qed.

(** Source for [coordinate_form_restriction_injective]: Federer
    1.6.6, p. 27, complex basis of real forms. The comparison loses
    no complex form, because every complex coordinate basis vector
    occurs in the image of a real basis vector. *)
Lemma coordinate_form_restriction_injective m : injective (@coordinate_form_restriction m).
Proof.
move=> a b h; apply: (form_basis_values_ext hC (coordinate_basisP C n)) => l.
have ht := congr1 (fun f : complex_valued_form embed U C^o m => f [tuple of map e (val l)]) h.
by rewrite !coordinate_restriction_basis_values in ht.
Qed.
(** Source for [coordinate_form_basis]: Federer 1.6.6, p. 27,
    complex basis of real forms. The ordinary Grassmann-coordinate
    basis over C, prior to restriction to the real space. *)
Definition coordinate_form_basis m (l : Lambda n m) : A_m E C^o m :=
  alternating_coordinate_basis (finite_e_lambda_basis (coordinate_basisP C n) hC m) l.

(** Source for [coordinate_form_basisP]: Federer 1.6.6, p. 27,
    complex basis of real forms. The source coordinate forms form a C-basis. *)
Lemma coordinate_form_basisP m : is_basis (@coordinate_form_basis m).
Proof. exact: alternating_coordinate_basisP. Qed.

(** Source for [coordinate_form_basis_values]: Federer 1.6.6,
    p. 27, complex basis of real forms. The source coordinate basis
    is biorthogonal to the increasing coordinate-vector tuples. *)
Lemma coordinate_form_basis_values m (l k : Lambda n m) :
  coordinate_form_basis l [tuple of map eb (val k)] = if l == k then 1 else 0.
Proof.
rewrite -pairing_e_lambda /coordinate_form_basis /alternating_coordinate_basis
  pairing_hom_identification /pairing_hom dual_basisE.
by rewrite eq_sym.
Qed.

(** Source for [restricted_coordinate_basisP]: Federer 1.6.6,
    p. 27, complex basis of real forms. Restricting the complex
    Grassmann-coordinate basis gives a basis of every real alternating
    form with complex coefficients, including degree zero. *)
Lemma restricted_coordinate_basisP m :
  is_basis (fun l : Lambda n m => coordinate_form_restriction (coordinate_form_basis l)).
Proof.
apply: (@complex_form_biorthogonal_basis R C embed U m hR n e he).
by move=> l k; rewrite coordinate_restriction_basis_values coordinate_form_basis_values.
Qed.

(** Source for [coordinate_form_restriction_surjective]: Federer
    1.6.6, p. 27, complex basis of real forms. Every complex-valued
    real alternating form extends to the complex coordinate space.
    This is a proved coordinate comparison, not an assumed complexification. *)
Theorem coordinate_form_restriction_surjective m :
  forall a : complex_valued_form embed U C^o m,
  exists b : A_m E C^o m, coordinate_form_restriction b = a.
Proof.
exact (@basis_map_surjective C (Choice.clone (Lambda n m) _)
  (A_m E C^o m) (complex_valued_form embed U C^o m)
  (@coordinate_form_basis m)
  (GRing.Linear.clone _ _ _ _ (@coordinate_form_restriction m) _)
  (restricted_coordinate_basisP m)).
Qed.
(** Source for [coordinate_form_extension]: Federer 1.6.6,
    p. 27, complex basis of real forms. The unique complex coordinate
    extension, obtained from the proved bijective restriction map. *)
Definition coordinate_form_extension m :=
  linear_inverse (@coordinate_form_restriction_injective m)
    (@coordinate_form_restriction_surjective m).

(** Source for [coordinate_form_extension_linear]: Federer
    1.6.6, p. 27, complex basis of real forms. Extension is C-linear. *)
Lemma coordinate_form_extension_linear m : linear (@coordinate_form_extension m).
Proof. exact: linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build C
  (complex_valued_form embed U C^o m) (A_m E C^o m) *:%R
  (@coordinate_form_extension m) (@coordinate_form_extension_linear m).

(** Source for [coordinate_form_extensionK]: Federer 1.6.6,
    p. 27, complex basis of real forms. Extension followed by restriction
    recovers every complex-valued real form. *)
Lemma coordinate_form_extensionK m :
  cancel (@coordinate_form_extension m) (@coordinate_form_restriction m).
Proof. exact: linear_inverseK. Qed.

(** Source for [coordinate_form_restrictionK]: Federer 1.6.6,
    p. 27, complex basis of real forms. Restriction followed by extension
    recovers every complex coordinate form. *)
Lemma coordinate_form_restrictionK m :
  cancel (@coordinate_form_restriction m) (@coordinate_form_extension m).
Proof. exact: linear_inverseKV. Qed.
End Coordinates.
