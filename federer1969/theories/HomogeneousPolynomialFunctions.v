(** Federer (1969), 1.10.4, pp. 45-46: homogeneous polynomial functions and
    polarization. The polynomial is an actual function. Existence of its
    representing form is a predicate; uniqueness follows from the proved
    polarization identity. Characteristic zero replaces the sources' real
    scalar field. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import TensorUP Bilinear Graded Hom HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricPolarizationCoefficients SymmetricPolarization SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Homogeneous.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation F := (GRing.Lmodule.clone K (V -> W) _).

(** Source for [sform_polynomial_value]: Federer 1.10.4,
    p. 45, defining display: evaluate a symmetric m-form on x^m/m!. *)
Definition sform_polynomial_value (f : S_m V W m) (x : V) : W :=
  sform_homogeneous f (symmetric_divided_vector_power x m).

(** Source for [sform_polynomial_linear]: Federer 1.10.4,
    p. 46, the first asserted linear isomorphism. Supporting linearity
    of the map from forms to actual functions. *)
Lemma sform_polynomial_linear : linear (sform_polynomial_value : S_m V W m -> F).
Proof.
move=> a f g; apply: funext=> x.
by rewrite /sform_polynomial_value linearP hom_m_addE hom_m_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (S_m V W m) F *:%R
  sform_polynomial_value sform_polynomial_linear.

(** Source for [is_homogeneous_polynomial]: Federer 1.10.4,
    p. 45, opening definition. A function is homogeneous polynomial
    of degree m precisely when it is represented by a symmetric m-form
    with the displayed factorial normalization. The zero function is
    homogeneous of every degree. *)
Definition is_homogeneous_polynomial (P : V -> W) : Prop :=
  exists f : S_m V W m, P =1 sform_polynomial_value f.

(** Source for [sform_polynomial_scale_argument]: Federer
    1.10.4, p. 46, scaling used in the formula for P(t*x).
    A homogeneous term scales by t^m. *)
Lemma sform_polynomial_scale_argument (f : S_m V W m) t x :
  sform_polynomial_value f (t *: x) = t^+m *: sform_polynomial_value f x.
Proof.
rewrite /sform_polynomial_value /symmetric_divided_vector_power
  symmetric_vector_power_scale !linearZ.
by [].
Qed.

(** Source for [sform_polynomial_polarization]: Federer
    1.10.4, p. 46, appeal to polarization in 1.9.3. The weighted
    sum of polynomial values at all signed sums recovers 2^m times
    the value of the symmetric form on the original tuple. *)
Lemma sform_polynomial_polarization (h0 : [pchar K] =i pred0)
    (f : S_m V W m) (v : m.-tuple V) :
  \sum_(t : polarization_signs m) polarization_sign_weight K t *:
    sform_polynomial_value f (\sum_i (polarization_sign K (t i)) *: tnth v i) =
    (2%:R : K)^+m *: f v.
Proof.
have h := congr1 (sform_homogeneous f) (symmetric_polarization_formula h0 (tnth v)).
move: h.
rewrite linear_sum linearZ map_tnth_enum.
under eq_bigr do rewrite linearZ.
move=> he.
change (\sum_(t : polarization_signs m) polarization_sign_weight K t *:
  sform_polynomial_value f (\sum_i (polarization_sign K (t i)) *: tnth v i) =
  (2%:R : K)^+m *: sform_homogeneous f (symmetric_word v)) in he.
by rewrite sform_homogeneousE sform_extensionE sform_wordsE in he.
Qed.

(** Source for [sform_polynomial_injective]: Federer 1.10.4,
    p. 46, polarization shows that P=0 iff its form is zero.
    The stronger equality formulation proves uniqueness of every
    representing form, with no dimension restriction. *)
Theorem sform_polynomial_injective (h0 : [pchar K] =i pred0) :
  injective sform_polynomial_value.
Proof.
move=> f g hfg; apply: sform_ext=> v.
have h := sform_polynomial_polarization h0 f v.
have h' := sform_polynomial_polarization h0 g v.
have he : (2%:R : K)^+m *: f v = (2%:R : K)^+m *: g v.
  rewrite -h -h'; apply: eq_bigr=> t _.
  by rewrite hfg.
have h2 : (2%:R : K) != 0 by move/pcharf0P: h0=> h0; rewrite h0.
have hp : (2%:R : K)^+m != 0 := expf_neq0 m h2.
have hc := congr1 (fun z : W => ((2%:R : K)^+m)^-1 *: z) he.
by move: hc; rewrite !scalerA mulVf // !scale1r.
Qed.

(** Source for [sform_polynomial_zero_iff]: Federer 1.10.4,
    p. 46, the stated vanishing equivalence. *)
Theorem sform_polynomial_zero_iff (h0 : [pchar K] =i pred0) (f : S_m V W m) :
  (forall x, sform_polynomial_value f x = 0) <-> f = 0.
Proof.
split.
- move=> hf; apply: (@sform_polynomial_injective h0 f 0).
  apply: funext=> x; rewrite hf.
  by rewrite (linear0 sform_polynomial_value).
- move=> -> x; by rewrite (linear0 sform_polynomial_value).
Qed.
End Homogeneous.

(** Source for [homogeneous_polynomial_unique_representation]: Federer
    1.10.4, pp. 45-46, the homogeneous-polynomial definition and
    its unique symmetric form. Together with the proved linearity,
    this states the claimed linear identification onto exactly the
    functions specified by the definition. *)
Theorem homogeneous_polynomial_unique_representation (K : fieldType)
    (h0 : [pchar K] =i pred0) (V W : lmodType K) m (P : V -> W) :
  is_homogeneous_polynomial m P ->
  exists f : S_m V W m, P =1 sform_polynomial_value f /\
    forall g : S_m V W m, P =1 sform_polynomial_value g -> g=f.
Proof.
move=> [f hf]; exists f; split=> // g hg.
apply: (@sform_polynomial_injective K V W m h0 g f); apply: funext=> x.
by rewrite -hf -hg.
Qed.
