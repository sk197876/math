(** Federer (1969), 1.6.6, p. 26: A_C^*(V,C) is the direct sum of the
    complex-multilinear homogeneous spaces and is a complex subalgebra of
    A^*(V,C). The defining predicate is componentwise; the finite
    decomposition and closure properties are proved below. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingSum AlternatingUnit
  AlgebraUP TensorUP Bilinear ScalarRestriction ComplexScalarSealed ComplexCharacteristic
  ComplexCoefficientAlgebra ComplexAlternatingForms ComplexFormConjugation
  ComplexFormProducts ComplexAlgebraScalars ScalarRestrictionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Subalgebra.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation hR := (real_two_nonzero R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Local Notation CR := (complex_real_algebra R).
Local Notation A := (alternating_unital_algebra hR VR CR).
Local Notation P m a := (@complex_multilinear_form R C embed V C^o m a).

(** Source for [complex_star_form]: Federer 1.6.6, p. 26,
    definition of A_C^*. Every homogeneous component is complex
    multilinear; finite support is already part of A^*. *)
Definition complex_star_form (a : A) := forall m, P m (form_component m a).

(** Source for [complex_real_zero]: Federer 1.6.6, p. 26,
    complex subspace assertion. The zero homogeneous form is complex. *)
Lemma complex_real_zero m : P m 0.
Proof. by move=> s t h c x y; rewrite !form_zeroE scaler0 add0r. Qed.

(** Source for [complex_real_add]: Federer 1.6.6, p. 26,
    complex subspace assertion. Homogeneous complex forms are closed
    under addition. *)
Lemma complex_real_add m (a b : A_m VR CR m) : P m a -> P m b -> P m (a+b).
Proof.
move=> ha hb s t h c x y; rewrite !form_addE.
by rewrite (ha s t h) (hb s t h) scalerDr addrACA.
Qed.

(** Source for [complex_real_scale]: Federer 1.6.6, p. 26,
    complex subspace assertion. Homogeneous complex forms are closed
    under multiplication by every complex scalar. *)
Lemma complex_real_scale m z (a : A_m VR CR m) : P m a -> P m (complex_scale_form z a).
Proof.
move=> ha s t h c x y; rewrite !complex_scale_formE (ha s t h).
change (z * (c * a (context_tuple s t h x) + a (context_tuple s t h y)) =
 c * (z * a (context_tuple s t h x)) + z * a (context_tuple s t h y)).
by rewrite mulrDr mulrCA.
Qed.

(** Source for [complex_star_zero]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. The zero element belongs. *)
Lemma complex_star_zero : complex_star_form 0.
Proof. by move=> m; rewrite linear0; exact: complex_real_zero. Qed.

(** Source for [complex_star_add]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. Closure under addition. *)
Lemma complex_star_add a b : complex_star_form a -> complex_star_form b -> complex_star_form (a+b).
Proof. by move=> ha hb m; rewrite linearD; apply: complex_real_add. Qed.

(** Source for [complex_star_include]: Federer 1.6.6, p. 26,
    direct-sum definition. Inclusion of every complex homogeneous form. *)
Lemma complex_star_include m (a : A_m VR CR m) : P m a -> complex_star_form (form_include a).
Proof.
move=> ha k; case: (eqVneq k m) => [->|hkm]; first by rewrite form_includeK.
have hz : form_component k (form_include a) = 0.
  apply: (can_inj (@form_includeK R VR CR k)).
  by rewrite form_componentK form_include_grade (negbTE hkm) linear0.
by rewrite hz; exact: complex_real_zero.
Qed.

(** Source for [complex_star_decomposition]: Federer 1.6.6,
    p. 26, direct-sum definition. Every member is a finite sum of
    included complex forms, with no finite-dimensional hypothesis on V. *)
Theorem complex_star_decomposition a : complex_star_form a ->
  exists N, exists b : forall m, A_m V C^o m,
    a = \sum_(j < N) form_include (restrict_form embed (b j)).
Proof.
move=> ha; have [N hN] := alternating_sum_decomposition a.
exists N; exists (fun m => @complex_form R C embed V C^o m (form_component m a) (ha m)).
apply: (eq_trans hN); apply: eq_bigr => j _; by rewrite restrict_complex_form.
Qed.

(** Source for [complex_star_finite_sum]: Federer 1.6.6,
    p. 26, direct-sum definition. Every finite sum of included
    complex forms satisfies the componentwise specification. *)
Lemma complex_star_finite_sum N (b : forall m, A_m V C^o m) :
  complex_star_form (\sum_(j < N) form_include (restrict_form embed (b j))).
Proof.
apply: big_ind => [|x y hx hy|]; [exact: complex_star_zero | exact: complex_star_add hx hy |].
move=> j _; apply: complex_star_include; exact: restrict_form_complex.
Qed.

(** Source for [complex_star_scale_component]: Federer 1.6.6,
    p. 26, complex algebra structure. Scalar action commutes with
    projection to every homogeneous component. *)
Lemma complex_star_scale_component m z (a : A) :
  form_component m (complex_algebra_scale (h2:=hR) z a) =
  complex_scale_form z (form_component m a).
Proof.
apply: form_ext => t.
by rewrite form_componentE complex_algebra_scaleE complex_scale_formE form_componentE.
Qed.

(** Source for [complex_star_scale]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. Closure under all complex scalars. *)
Lemma complex_star_scale z a : complex_star_form a ->
  complex_star_form (complex_algebra_scale (h2:=hR) z a).
Proof. by move=> ha m; rewrite complex_star_scale_component; apply: complex_real_scale. Qed.

(** Source for [complex_star_unit]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. Every constant coefficient belongs,
    in particular the unit. *)
Lemma complex_star_unit z : complex_star_form (@coefficient_form R VR CR z).
Proof.
apply: complex_star_include => s t h c x y.
exfalso; by move: h; rewrite size_cat /= addnS.
Qed.

(** Source for [complex_star_product]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. Multiplication preserves complex
    multilinearity of all components, by the finite decompositions
    and the homogeneous product comparison. *)
Theorem complex_star_product a b : complex_star_form a -> complex_star_form b ->
  complex_star_form (alg_mul A a b).
Proof.
move=> ha hb.
have [N [f ->]] := complex_star_decomposition ha.
have [M [g ->]] := complex_star_decomposition hb.
rewrite (big_morph (fun x => alg_mul A x _) (fun x y => bilDl (alg_bilinear A) x y _) (bil0l (alg_bilinear A) _)).
apply: big_ind => [|x y hx hy|]; [exact: complex_star_zero | exact: complex_star_add hx hy |].
move=> j _; rewrite (big_morph (alg_mul A _) (bilDr (alg_bilinear A) _) (bil0r (alg_bilinear A) _)).
apply: big_ind => [|x y hx hy|]; [exact: complex_star_zero | exact: complex_star_add hx hy |].
move=> k _.
change (complex_star_form (alternating_wedge hR (alg_bilinear CR)
  (form_include (restrict_form embed (f j))) (form_include (restrict_form embed (g k))))).
rewrite -form_wedge_include -(@restrict_form_wedge R C hR hC embed V C^o
  *%R (scalar_bilinear C) (alg_bilinear CR)).
apply: complex_star_include; exact: restrict_form_complex.
Qed.
End Subalgebra.
