(** Federer (1969), 1.6.6, p. 27: the complex volume and its conjugate
    product used in the determinant calculation. The nonvanishing follows
    from the proved mixed basis, including n=0. Source context are recorded
    in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlgebraUP OneFormProducts
  ScalarRestriction ComplexScalarSealed ComplexCharacteristic ComplexCoefficientAlgebra
  ComplexAlternatingForms ComplexValuedForms ComplexFormConjugation
  ComplexMixedForms ComplexOrderedBases ComplexOneFormBasis ComplexProductBasis
  ComplexFormWords ComplexWordRestriction FormWordOperations CovectorProductNaturality
  CovectorProducts ConcatenatedFamilies ExteriorDeterminant DualityAnnihilator
  OneFormIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Top.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Local Notation hR := (real_two_nonzero R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [complex_top_form]: Federer 1.6.6, p. 27,
    alpha=alpha_1 wedge ... wedge alpha_n in the volume display. *)
Definition complex_top_form := holomorphic_basis_form he (Lambda_top n).

(** Source for [complex_top_volume]: Federer 1.6.6, p. 27,
    alpha wedge bar(alpha), the separated complex volume blocks. *)
Definition complex_top_volume : A_m VR CR (n+n) :=
  form_wedge hR (alg_bilinear CR) (restrict_form embed complex_top_form)
    (conjugate_form (restrict_form embed complex_top_form)).

(** Source for [complex_top_volume_mixed]: Federer 1.6.6,
    p. 27, mixed basis and separated volume display. The complex
    volume is the top member of the mixed basis. *)
Lemma complex_top_volume_mixed :
  mixed_complex_form he (Lambda_top (n+n)) = real_as_complex_valued complex_top_volume.
Proof.
rewrite /mixed_complex_form /complex_values_lambda.
have ht : (fun j => ordered_mixed_one_form he (tnth (val (Lambda_top (n+n))) j)) =
  ordered_mixed_one_form he.
  by apply: boolp.funext => j; rewrite /Lambda_top tnth_ord_tuple.
rewrite ht /complex_values_word /complex_top_volume /complex_top_form
  /holomorphic_basis_form omega_lambda_top_product restrict_one_forms_wedge.
have hc : conjugate_form
    (one_forms_wedge hR (alg_bilinear CR) (1:C)
      (fun j => restrict_form embed (one_form (dual_basis he j)))) =
  one_forms_wedge hR (alg_bilinear CR) (1:C)
      (fun j => conjugate_form (restrict_form embed (one_form (dual_basis he j)))).
  exact: (@one_forms_wedge_coefficients R hR VR CR CR (complex_conjugation_map R)).
rewrite hc -one_forms_wedge_concatenate.
congr (real_as_complex_valued (one_forms_wedge hR (alg_bilinear CR) (1:C) _)).
apply: boolp.funext => j.
rewrite /ordered_mixed_one_form /concatenate_family.
by case: (split j).
Qed.

(** Source for [complex_top_volume_nonzero]: Federer 1.6.6,
    p. 27, nonzero volume used for the determinant comparison. The
    mixed top basis element is nonzero, also in complex dimension zero. *)
Theorem complex_top_volume_nonzero : complex_top_volume != 0.
Proof.
apply/eqP => hz.
have hn := basis_vector_nonzero (mixed_complex_form_basis he (n+n)) (Lambda_top (n+n)).
rewrite complex_top_volume_mixed hz in hn.
have h0 : real_as_complex_valued (0 : A_m VR CR (n+n)) = 0.
  by apply: complex_valued_form_ext => t.
by rewrite h0 eqxx in hn.
Qed.
End Top.

(** Source for [complex_scale_form_injective]: Federer 1.6.6,
    p. 27, comparing the two factors of a nonzero volume. Scalar
    multiples of a nonzero complex-valued real form determine the scalar. *)
Lemma complex_scale_form_injective (R : realFieldType) (U : lmodType R)
  m (a : A_m U (complex_real_algebra R) m) : a != 0 ->
  injective (fun z => complex_scale_form z a).
Proof.
move=> ha.
pose b := real_as_complex_valued a.
have hb : b != 0.
  apply/eqP => hz.
  have haz : a = 0.
    apply: form_ext => t.
    have h := congr1 (fun f : complex_valued_form (ComplexScalars.embed R) U (ComplexScalars.C R)^o m => f t) hz.
    exact h.
  by rewrite haz eqxx in ha.
move=> c d h.
have hcd : c *: b = d *: b.
  apply: complex_valued_form_ext => t.
  have ht := congr1 (fun f : A_m U (complex_real_algebra R) m => f t) h.
  by rewrite !complex_scale_formE in ht.
have hz : (c-d) *: b = 0 by rewrite scalerBl hcd subrr.
have /eqP hc : c-d == 0.
  by move/eqP: hz; rewrite scaler_eq0 (negbTE hb) orbF.
exact: subr0_eq hc.
Qed.
