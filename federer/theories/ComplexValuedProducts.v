(** Federer (1969), 1.6.6, p. 26: the complex algebra structure on real
    alternating forms and its complex multilinear subspace. Products here
    are the existing real alternating products; their complex bilinearity
    and compatibility with complex forms are proved. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates TensorUP Bilinear
  ScalarRestriction ScalarRestrictionProduct ComplexScalarSealed ComplexCharacteristic
  ComplexCoefficientAlgebra ComplexValuedForms ComplexAlternatingForms ComplexFormSubspace
  ComplexFormConjugation ComplexFormProducts ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Valued.
Variable R : realFieldType.
Hypothesis hR : (1+1 : R) != 0.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Variable U : lmodType R.
Local Notation CF m := (complex_valued_form embed U C^o m).

(** Source for [complex_values_real_add]: Federer 1.6.6,
    p. 26, complex scalar structure on real forms. Supporting
    compatibility of the two carriers with addition. *)
Lemma complex_values_real_add m (a b : CF m) :
  complex_valued_as_real (a+b) = complex_valued_as_real a + complex_valued_as_real b.
Proof. by apply: form_ext. Qed.

(** Source for [complex_values_real_scale]: Federer 1.6.6,
    p. 26, complex scalar structure on real forms. The scalar operation
    on the complex carrier agrees with multiplication of form values. *)
Lemma complex_values_real_scale m z (a : CF m) :
  complex_valued_as_real (z *: a) = complex_scale_form z (complex_valued_as_real a).
Proof. by apply: form_ext => t; rewrite complex_scale_formE. Qed.

(** Source for [complex_values_wedge]: Federer 1.6.6, p. 26,
    complex algebra of real alternating forms. The existing real
    alternating product on the complex coefficient carrier. *)
Definition complex_values_wedge p q (a : CF p) (b : CF q) : CF (p+q) :=
  real_as_complex_valued (form_wedge hR (alg_bilinear CR)
    (complex_valued_as_real a) (complex_valued_as_real b)).

(** Source for [complex_values_wedge_real]: Federer 1.6.6,
    p. 26, complex algebra of real forms. Compatibility with the
    already defined real alternating product. *)
Lemma complex_values_wedge_real p q (a : CF p) (b : CF q) :
  complex_valued_as_real (complex_values_wedge a b) =
  form_wedge hR (alg_bilinear CR) (complex_valued_as_real a) (complex_valued_as_real b).
Proof. exact: real_complex_valuedK. Qed.

(** Source for [complex_values_wedge_bilinear]: Federer 1.6.6,
    p. 26, complex algebra assertion. The product is bilinear over C,
    even though its arguments are only real multilinear forms. *)
Lemma complex_values_wedge_bilinear p q : bilinear (@complex_values_wedge p q).
Proof.
split=> b z a a'; apply: (can_inj (@complex_valued_realK R C embed U C^o (p+q)));
  rewrite complex_values_wedge_real complex_values_real_add complex_values_real_scale
    complex_values_real_add complex_values_real_scale !complex_values_wedge_real.
- by rewrite (bilDl (form_wedge_bilinear hR U (alg_bilinear CR) p q))
    -complex_scale_wedge_left.
- by rewrite (bilDr (form_wedge_bilinear hR U (alg_bilinear CR) p q))
    -complex_scale_wedge_right.
Qed.
End Valued.

Section ComplexInputs.
Variable R : realFieldType.
Hypothesis hR : (1+1 : R) != 0.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).

(** Source for [complex_inclusion_wedge]: Federer 1.6.6,
    p. 26, complex subalgebra assertion. Inclusion of complex
    multilinear forms preserves the alternating product. *)
Lemma complex_inclusion_wedge p q (a : A_m V C^o p) (b : A_m V C^o q) :
  complex_form_inclusion embed (form_wedge (complex_two_nonzero R) (scalar_bilinear C) a b) =
  complex_values_wedge hR (complex_form_inclusion embed a) (complex_form_inclusion embed b).
Proof.
apply: (can_inj (@complex_valued_realK R C embed VR C^o (p+q))).
change (restrict_form embed (form_wedge (complex_two_nonzero R) (scalar_bilinear C) a b) =
  form_wedge hR (alg_bilinear CR) (restrict_form embed a) (restrict_form embed b)).
exact: restrict_form_wedge.
Qed.

(** Source for [complex_subspace_wedge_closed]: Federer 1.6.6,
    p. 26, complex subalgebra assertion. Products of complex multilinear
    forms satisfy the same defining condition, in the sum of the degrees. *)
Theorem complex_subspace_wedge_closed p q
    (a : complex_valued_form embed VR C^o p) (b : complex_valued_form embed VR C^o q) :
  @complex_form_subspace R C embed V C^o p a ->
  @complex_form_subspace R C embed V C^o q b ->
  @complex_form_subspace R C embed V C^o (p+q) (complex_values_wedge hR a b).
Proof.
move=> ha hb.
have [a' ea] := proj1 (@complex_form_subspace_image R C embed V C^o p a) ha.
have [b' eb] := proj1 (@complex_form_subspace_image R C embed V C^o q b) hb.
rewrite -ea -eb -complex_inclusion_wedge.
apply/( @complex_form_subspace_image R C embed V C^o (p+q)); by eexists.
Qed.
End ComplexInputs.
