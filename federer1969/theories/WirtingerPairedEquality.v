(** Federer (1969), 1.8.2, p. 40: sufficiency of the
    paired-product equality criterion in arbitrary ambient dimension.
    A nonzero paired product is reduced to the finite complex span
    of its factors; a zero product is handled directly. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors ScalarRestriction ComplexScalarSealed
  ComplexPairedVectors ComplexPairedPlanes ComplexPairedNaturality
  SubspaceCarrier FiniteSpanSpace HermitianUP HermitianRealImaginary
  HermitianRotation HermitianPullback TwoFormPowers TwoFormPowerNaturality
  ExteriorNorm ExteriorNormNaturality WirtingerBasisEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [wirtinger_paired_equality]: Federer 1.8.2,
    p. 40, every product v_1 wedge i v_1 wedge ... wedge v_m
    wedge i v_m attains equality. Neither independence of the
    factors nor finite ambient dimension is required. *)
Theorem wirtinger_paired_equality (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType (ComplexScalars.C R))
    (H : V -> V -> ComplexScalars.C R) (hH : is_hermitian_product H)
    m (v : 'I_m -> V) :
  pairing (paired_complex_vector v) (two_form_power h2 (hermitian_two_form hH) m) =
    m`!%:R * exterior_norm h2 (hermitian_real_inner_product hH) (paired_complex_vector v).
Proof.
pose C := ComplexScalars.C R.
pose VR := restricted_space (ComplexScalars.embed R) V.
case hv0 : (paired_complex_vector v == 0).
- move/eqP: hv0=> ->.
  by rewrite (bil0l (@pairing_bilinear R VR R^o (m+m))) exterior_norm_zero mulr0.
- have hv : paired_complex_vector v != 0 by rewrite hv0.
  pose S := finite_span_subspace v.
  pose U := GRing.Lmodule.clone C (subspace_space S) _.
  pose f : {linear U -> V} := subspace_inclusion S.
  have hf : injective f := @subspace_val_injective C V S.
  pose D := hermitian_pullback H f.
  pose hD := hermitian_pullbackP hH hf.
  pose a : 'I_m -> U := finite_span_basis v.
  have ha : is_basis a := finite_span_basisP (paired_vector_independent hv).
  have he := wirtinger_complex_basis_equality h2 hD ha.
  pose fr := restrict_linear (ComplexScalars.embed R) f.
  have hmap : exterior_power_map fr (m+m) (paired_complex_vector a) = paired_complex_vector v.
    exact: paired_complex_vector_natural.
  rewrite hermitian_pullback_two_form -two_form_power_natural A_m_dual_pairing in he.
  rewrite -hmap.
  rewrite (@exterior_norm_orthogonal_natural R h2
    (restricted_space (ComplexScalars.embed R) U) VR
    (hermitian_real_part D) (hermitian_real_part H)
    (hermitian_real_inner_product hD) (hermitian_real_inner_product hH)
    fr (hermitian_pullback_orthogonal H f)).
  exact he.
Qed.
