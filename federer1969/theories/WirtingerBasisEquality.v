(** Federer (1969), 1.8.2, p. 40: every complex paired
    product has equality in Wirtinger's inequality. This intermediate
    result treats a complex basis of the entire space. An orthonormal
    paired basis gives the unit computation; the positive change of
    complex orientation from 1.6.6 gives the general basis case. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors ScalarRestriction ComplexScalarSealed
  ComplexOrderedBases ComplexPairedVectors ComplexPairedPlanes
  ComplexPlaneOrientation HermitianUP HermitianRealImaginary HermitianRotation
  HermitianPairedBasis PairedBasisCardinality PairedComplexSpan
  PairedRealVectors PairedVectorNaturality NormalPowerUnitBound
  TwoFormPowers ExteriorNorm InnerPolarity SkewNormalFormUP FiniteSpans ComplexRealBasis Annihilator OrthonormalBilinearCoordinates Hom FiniteDualDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [wirtinger_complex_basis_equality]: Federer 1.8.2,
    p. 40, the sufficiency of the paired-product condition, first
    for a complex basis. Positive orientation is essential; this
    does not replace the signed pairing by an absolute value. *)
Theorem wirtinger_complex_basis_equality (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType (ComplexScalars.C R))
    (H : V -> V -> ComplexScalars.C R) (hH : is_hermitian_product H)
    m (v : 'I_m -> V) (hv : is_basis v) :
  pairing (paired_complex_vector v) (two_form_power h2 (hermitian_two_form hH) m) =
    m`!%:R * exterior_norm h2 (hermitian_real_inner_product hH) (paired_complex_vector v).
Proof.
pose VR := restricted_space (ComplexScalars.embed R) V.
pose B := hermitian_real_part H.
pose hB := hermitian_real_inner_product hH.
have [k [a [ho [ha hA]]]] := hermitian_orthonormal_paired_basis hH h2 (ordered_real_basisP hv).
have hkm := @paired_basis_count R VR m (ordered_real_basis v) (ordered_real_basisP hv)
  k a (fun i => hermitian_rotation (a i)) ha.
subst k.
have hu : exterior_norm h2 hB (paired_complex_vector a) = 1.
  rewrite -paired_real_complex_identification.
  exact (@paired_orthonormal_vector_unit R h2 VR B hB m a
    (fun i => hermitian_rotation (a i)) ho).
have ha0 : paired_complex_vector a != 0.
  by rewrite -(exterior_norm_eq0 h2 hB) hu oner_eq0.
have hv0 := paired_complex_vector_nonzero hv.
have heq z : FedererSimple.T (paired_complex_vector a) z <->
    FedererSimple.T (paired_complex_vector v) z.
  rewrite (paired_vector_complex_span ha0) (paired_vector_complex_span hv0).
  split=> _.
  - exists (fun i => dual_basis hv i z); exact (@basis_vector_expansion (ComplexScalars.C R) V m v hv z).
  - exact: paired_real_basis_complex_span ha z.
have [d [hd he]] := paired_planes_positive_multiple ha0 hv0 heq.
have hp : pairing (paired_complex_vector a)
    (two_form_power h2 (hermitian_two_form hH) m) = m`!%:R.
  rewrite hA -paired_real_complex_identification.
  have hA' : (\sum_j form_wedge h2 (scalar_bilinear R)
      (inner_polarity hB (a j)) (inner_polarity hB (hermitian_rotation (a j)))) =
    \sum_j (1 : R) *: form_wedge h2 (scalar_bilinear R)
      (inner_polarity hB (a j)) (inner_polarity hB (hermitian_rotation (a j))).
    apply: eq_bigr => j _; by rewrite scale1r.
  rewrite hA'.
  exact (proj2 (@normal_two_form_unit_equality R h2 VR B hB m a
    (fun i => hermitian_rotation (a i)) (fun _ => 1) ho
    (fun _ => ler01) (fun _ => lexx 1)
    (@paired_real_vector R VR m a (fun i => hermitian_rotation (a i)))
    (paired_orthonormal_vector_unit h2 hB ho)) (conj erefl (fun _ => erefl))).
rewrite he (bilZl (@pairing_bilinear R VR R^o (m+m))) exterior_norm_scale hu.
by rewrite hp (ger0_norm (ltW hd)) mulr1 mulrC.
Qed.
