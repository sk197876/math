(** Federer (1969), 1.8.2, p. 40: orthonormal complex
    pairs realise the sharp comass and the positive equality case.
    The existence argument below applies the already proved skew
    normal form from 1.7.3, pp. 29-30, to J(v)=iv. It does not
    introduce a coordinate definition of a Hermitian product. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HermitianUP
  HermitianRealImaginary HermitianRotation InnerProductUP OrthogonalMaps
  OrthonormalFamilies LinearBasis SymmetricEndomorphisms SkewNormalFormUP
  SkewNormalFormSealed SkewNormalVectorActions SkewNormalFullBasis
  AlternatingForms AlternatingProduct ScalarCoefficients InnerPolarity
  TwoCovectorProduct FormEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Basis.
Variable R : realType.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Hypothesis h2 : (1+1 : R) != 0.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Local Notation B := (hermitian_real_part H).
Local Notation hB := (hermitian_real_inner_product hH).
Local Notation J := (GRing.Linear.clone R VR VR *:%R (@hermitian_rotation R V) _).

(** Source for [hermitian_rotation_skew]: Federer 1.8.2,
    pp. 39-40, the operator J corresponds to the alternating form A. *)
Lemma hermitian_rotation_skew : is_skewsymmetric_endomorphism B J.
Proof.
move=> x y; change (B (hermitian_rotation x) y = - B x (hermitian_rotation y)).
rewrite (inner_symmetric hB x) -!(hermitian_imaginary_rotation hH).
exact: hermitian_imaginary_part_skew hH y x.
Qed.

(** Source for [hermitian_orthonormal_paired_basis]: Federer 1.8.2,
    p. 40, supporting existence of a full orthonormal family of
    pairs a_j,i a_j in finite dimension, with A the sum of their
    polarity wedge products. The empty space is included. *)
Theorem hermitian_orthonormal_paired_basis n (e : 'I_n -> VR) (he : is_basis e) :
  exists k (a : 'I_k -> V),
    orthonormal_family B (paired_family a (fun i => hermitian_rotation (a i))) /\
    @is_basis R (Choice.clone ('I_k * bool)%type _) VR
      (paired_family a (fun i => hermitian_rotation (a i))) /\
    hermitian_two_form hH = \sum_j form_wedge h2 (scalar_bilinear R)
      (inner_polarity hB (a j)) (inner_polarity hB (hermitian_rotation (a j))).
Proof.
have [k [a [b [lambda [ho [hl hn]]]]]] :=
  @SkewNormalForm.exists_blocks R VR B hB n e he J hermitian_rotation_skew.
have hj : is_orthogonal_map B B J := hermitian_rotation_orthogonal hH.
have hcoeff i : lambda i = 1 :=
  orthogonal_skew_normal_coefficients_one hB ho hn hj hl i.
have hab i : b i = hermitian_rotation (a i).
  have ha := skew_normal_first_action hB ho hn i.
  by rewrite hcoeff scale1r in ha; exact: esym ha.
have hsurj x : exists y, J y = x.
  exists (- hermitian_rotation x); rewrite linearN.
  by change (-hermitian_rotation (hermitian_rotation x) = x);
    rewrite hermitian_rotation_square opprK.
have hb := surjective_skew_normal_basis hB ho hn hsurj.
have hp p : paired_family a b p = paired_family a (fun i => hermitian_rotation (a i)) p.
  by case: p => [i []]; rewrite /paired_family /= ?hab.
exists k, a; split.
- move=> p q; by rewrite -!hp ho.
- split; first exact: basis_congr hp hb.
  apply: form_ext => /tupleP [x t]; case/tupleP: t => y t; rewrite (tuple0 t).
  rewrite hermitian_two_formE.
  change (B (J x) y = form_evaluate [tuple x; y]
    (\sum_j form_wedge h2 (scalar_bilinear R)
      (inner_polarity hB (a j)) (inner_polarity hB (hermitian_rotation (a j))))).
  rewrite linear_sum.
  change (B (J x) y = \sum_j
    form_wedge h2 (scalar_bilinear R) (inner_polarity hB (a j))
      (inner_polarity hB (hermitian_rotation (a j))) [tuple x; y]).
  rewrite hn; apply: eq_bigr => j _.
  by rewrite hcoeff mul1r hab inner_covector_pair_product.
Qed.
End Basis.
