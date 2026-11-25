(** Federer (1969), 1.6.6, p. 27: the plane spanned by v_1,i v_1,...,v_p,i
    v_p is a complex subspace. The real span of those factors is exactly the
    complex span of v_1,...,v_p. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ScalarRestriction ComplexScalarUP
  ComplexScalarSealed ComplexScalarLaws ComplexOrderedBases ComplexSubspaces
  FiniteSpans FiniteSpanSpace ConcatenatedFamilies FiniteBasisCriterion FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Span.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable p : nat.
Variable v : 'I_p -> V.

(** Source for [complex_span_real_combination]: Federer 1.6.6,
    p. 27, complex associated plane. A real combination of the paired
    factors is the complex combination with coefficients a_j+i b_j. *)
Lemma complex_span_real_combination (c : 'I_(p+p) -> R) :
  (\sum_j c j *: ordered_real_basis v j : VR) =
  \sum_j (embed (c (lshift p j)) + ii * embed (c (rshift p j))) *: v j.
Proof.
change ((\sum_j c j *: concatenate_family (fun j => (v j : VR)) (fun j => (ii *: v j : VR)) j) =
  \sum_j (embed (c (lshift p j)) + ii * embed (c (rshift p j))) *: v j).
rewrite concatenate_family_sum -big_split.
apply: eq_bigr => j _.
change (embed (c (lshift p j)) *: v j + embed (c (rshift p j)) *: (ii *: v j) =
  (embed (c (lshift p j)) + ii * embed (c (rshift p j))) *: v j).
by rewrite scalerDl scalerA mulrC.
Qed.

(** Source for [complex_span_complex_combination]: Federer
    1.6.6, p. 27, complex associated plane. Splitting each complex
    coefficient into real and imaginary parts gives a real combination. *)
Lemma complex_span_complex_combination (c : 'I_p -> C) :
  (\sum_j c j *: v j) =
  \sum_j concatenate_family (fun k => @ComplexScalars.re R (c k))
    (fun k => @ComplexScalars.im R (c k)) j *: ordered_real_basis v j.
Proof.
rewrite [RHS]complex_span_real_combination.
apply: eq_bigr => j _.
rewrite concatenate_family_l concatenate_family_r.
by rewrite -(complex_decomposition (ComplexScalars.laws R) (c j)).
Qed.

(** Source for [complex_real_span]: Federer 1.6.6, p. 27,
    complex associated plane. Exact equality of the real paired span
    and the complex span; no independence assumption is needed. *)
Theorem complex_real_span (x : V) :
  @in_finite_span R VR (p+p) (ordered_real_basis v) x <-> in_finite_span v x.
Proof.
split.
- move=> [c hc]; exists (fun j => embed (c (lshift p j)) + ii * embed (c (rshift p j))).
  by rewrite -complex_span_real_combination -hc.
- move=> [c ->].
  exists (concatenate_family (fun j => @ComplexScalars.re R (c j))
    (fun j => @ComplexScalars.im R (c j))).
  exact: complex_span_complex_combination.
Qed.

(** Source for [complex_block_span_stable]: Federer 1.6.6,
    p. 27, converse direction in the characterisation. The real
    span of paired factors is invariant under i. *)
Theorem complex_block_span_stable :
  complex_stable_subspace (finite_span_subspace (ordered_real_basis v)).
Proof.
move=> x hx; apply/complex_real_span.
apply: in_finite_span_scale.
exact: (proj1 (complex_real_span x) hx).
Qed.

(** Source for [complex_independent_blocks]: Federer 1.6.6,
    pp. 26-27, paired real bases. Complex independence implies real
    independence of all the original and imaginary basis vectors. *)
Lemma complex_independent_blocks : finite_independent v ->
  @finite_independent R 'I_(p+p) VR (ordered_real_basis v).
Proof.
move=> hv c hc i.
have hz : \sum_j (embed (c (lshift p j)) + ii * embed (c (rshift p j))) *: v j = 0.
  by rewrite -complex_span_real_combination hc.
have ht j := hv (fun j => embed (c (lshift p j)) + ii * embed (c (rshift p j))) hz j.
have hl j : c (lshift p j) = 0.
  have h := congr1 (@ComplexScalars.re R) (ht j).
  by rewrite (complex_re_add (ComplexScalars.laws R)) re_embed re_i_real addr0 re_zero in h.
have hr j : c (rshift p j) = 0.
  have h := congr1 (@ComplexScalars.im R) (ht j).
  by rewrite (complex_im_add (ComplexScalars.laws R)) im_embed im_i_real add0r im_zero in h.
rewrite -(splitK i); case: (split i) => j; [exact: hl | exact: hr].
Qed.

(** Source for [real_blocks_independent_complex]: Federer
    1.6.6, p. 27, the paired representation of a nonzero simple
    vector. Real independence of the paired factors implies complex
    independence of their unbarred members. *)
Lemma real_blocks_independent_complex :
  @finite_independent R 'I_(p+p) VR (ordered_real_basis v) -> finite_independent v.
Proof.
move=> hv c hc j.
pose r := concatenate_family (fun j => @ComplexScalars.re R (c j))
  (fun j => @ComplexScalars.im R (c j)).
have hz : \sum_i r i *: ordered_real_basis v i = 0.
  by rewrite /r -complex_span_complex_combination hc.
have hr := hv r hz (lshift p j).
have hi := hv r hz (rshift p j).
rewrite /r concatenate_family_l in hr.
rewrite /r concatenate_family_r in hi.
by apply: coordinates_injective; rewrite ?re_zero ?im_zero.
Qed.
End Span.
