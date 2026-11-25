(** Federer (1969), 1.6.6, p. 27: v_1 wedge i v_1 wedge ... wedge v_p wedge
    i v_p. The typed vector is expressed by the two-block product and its
    reordering sign; the equality to the literal interleaved word is proved.
    Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra binomial.
From Federer Require Import SimpleVectors SimpleElementary ComplexScalarSealed
  ComplexCharacteristic ScalarRestriction ComplexOrderedBases PairedGradedWords
  ConcatenatedFamilies WordEvaluation FiniteExteriorPowers DualityAnnihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Paired.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation hR := (real_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Variable p : nat.
Variable v : 'I_p -> V.

(** Source for [paired_complex_vector]: Federer 1.6.6,
    p. 27, the paired product in the characterisation of complex
    simple vectors. Its degree is p+p=2p. *)
Definition paired_complex_vector : exterior_power VR (p+p) :=
  (-1:R)^+'C(p,2) *: e_lambda (ordered_real_basis v) (ord_tuple (p+p)).

(** Source for [paired_complex_vector_word]: Federer 1.6.6,
    p. 27, v_1 wedge i v_1 wedge ... wedge v_p wedge i v_p.
    Identification with the literal interleaved exterior word. *)
Lemma paired_complex_vector_word : component_val paired_complex_vector =
  @exterior_word R VR (flatten [seq [:: v j; ii *: v j] | j <- enum 'I_p]).
Proof.
rewrite /paired_complex_vector linearZ.
change ((-1:R)^+'C(p,2) *: component_val (e_lambda (ordered_real_basis v) (ord_tuple (p+p))) =
  @exterior_word R VR (flatten [seq [:: v j; ii *: v j] | j <- enum 'I_p])).
rewrite e_lambdaE.
have h := @paired_word_interleaving_sign R (exterior_algebra VR) (exterior_grading VR)
  (@wedge_graded R VR) (@exterior_unit_homogeneous R VR) (@exterior_anticommutative R VR)
  (Choice.clone VR _) (@exterior_generator R VR) (@exterior_generator_homogeneous R VR)
  (Choice.clone 'I_p _) v (fun j => ii *: v j) (enum 'I_p).
have hw (s : seq VR) : @word_eval R (Choice.clone VR _) (exterior_algebra VR)
    (@exterior_generator R VR) s = @exterior_word R VR s.
  by elim: s => [|x s ih] //=; rewrite exterior_word_cons -ih.
rewrite !hw size_enum_ord in h.
have hl : [seq ordered_real_basis v j | j <- enum 'I_(p+p)] =
  [seq v j | j <- enum 'I_p] ++ [seq ii *: v j | j <- enum 'I_p].
  exact: concatenate_family_sequence.
rewrite hl -exterior_word_cat.
exact: esym h.
Qed.

(** Source for [paired_complex_vector_simple]: Federer 1.6.6,
    p. 27, the paired product is simple. The empty paired product
    is exactly the unit, respecting the literal degree-zero convention. *)
Lemma paired_complex_vector_simple : simple paired_complex_vector.
Proof.
rewrite /paired_complex_vector; case: p v => [|q] a.
- have hbin : 'C(0,2) = 0%N by [].
  rewrite hbin expr0 scale1r; exact: product_simple.
- apply: simple_scale; [by [] | exact: product_simple].
Qed.

(** Source for [paired_complex_vector_nonzero]: Federer
    1.6.6, p. 27, paired product of a complex basis. It is a nonzero
    real top vector, including the zero-dimensional unit. *)
Lemma paired_complex_vector_nonzero : is_basis v -> paired_complex_vector != 0.
Proof.
move=> hv; rewrite /paired_complex_vector scaler_eq0 signr_eq0 /=.
exact: (basis_vector_nonzero (finite_e_lambda_basis (ordered_real_basisP hv) hR (p+p)) (Lambda_top (p+p))).
Qed.

(** Source for [paired_complex_vector_associated]: Federer
    1.6.6, p. 27, complex associated plane. The reordering sign
    does not change the subspace associated with the paired product. *)
Lemma paired_complex_vector_associated x :
  FedererSimple.T paired_complex_vector x <->
  FedererSimple.T (e_lambda (ordered_real_basis v) (ord_tuple (p+p))) x.
Proof. apply: associated_scale_nonzero; by rewrite signr_eq0. Qed.
End Paired.
