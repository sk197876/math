(** Federer (1969), 1.10.5, p. 48, Hilbert-input norm equality attributed to
    [H 1]. This module extends the locally proved finite-dimensional scalar
    diagonal-maximum theorem to arbitrary input dimension and normed
    coefficient spaces. A norming functional handles the coefficient space;
    the finite span of a given tuple handles the input space. No
    boundedness, completeness or finite-dimensional output hypothesis is
    imposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerProductPullback InnerNorm
  LinearBasis FiniteSpans FiniteSpanSpace SubspaceCarrier SymmetricForms
  SymmetricFormDual SymmetricFormPostcompose SymmetricOperatorNormUP
  RealNormUP SeminormNormingFunctional FiniteHilbertDiagonalMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_hilbert_vector_diagonal_dominates]: Federer
    1.10.5, p. 48, supporting passage to arbitrary normed
    coefficients. A scalar functional norms the selected output value;
    its composition with the form has a scalar diagonal maximum. The
    coefficient seminorm version is a strengthening of the normed case. *)
Theorem finite_hilbert_vector_diagonal_dominates (R : realType)
    (V W : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (NW : W -> R) (hW : is_real_seminorm NW)
    n (e : 'I_n -> V) (he : is_basis e) m (f : S_m V W m) (t : m.-tuple V) :
  symmetric_form_unit_tuple (inner_norm hB) t ->
  exists x, inner_norm hB x<=1 /\ NW (f t)<=NW (f [tuple x | i<m]).
Proof.
move=> ht.
have [g [hg hgt]] := seminorm_norming_functional hW (f t).
have [x [hx hmax]] := @finite_hilbert_diagonal_maximum R V B hB n e he m
  (symmetric_form_postcompose g f).
exists x; split=> //.
have hh := hmax t ht.
rewrite !symmetric_form_postcomposeE hgt (ger0_norm (real_seminorm_nonnegative hW _)) in hh.
exact: le_trans hh (hg _).
Qed.

(** Source for [inner_pullback_norm]: Federer 1.10.5,
    p. 48, supporting isometry of a finite input subspace
    with its inherited inner product. Uniqueness of the nonnegative
    square root proves the equality of lengths. *)
Lemma inner_pullback_norm (R : rcfType) (U V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (j : {linear U -> V}) (hj : injective j) x :
  inner_norm (inner_product_linear_pullback hB hj) x = inner_norm hB (j x).
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
exact: inner_norm_sqr.
Qed.

(** Source for [hilbert_vector_diagonal_dominates]: Federer
    1.10.5, p. 48, supporting diagonal dominance in arbitrary
    dimension. Each individual unit tuple lies in a finite-dimensional
    inner-product subspace, where the proved scalarization and maximum
    argument applies. This is sufficient even when the form is unbounded. *)
Theorem hilbert_vector_diagonal_dominates (R : realType)
    (V W : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (NW : W -> R) (hW : is_real_seminorm NW)
    m (f : S_m V W m) (t : m.-tuple V) :
  symmetric_form_unit_tuple (inner_norm hB) t ->
  exists x, inner_norm hB x<=1 /\ NW (f t)<=NW (f [tuple x | i<m]).
Proof.
move=> ht.
have [n [e [he hspan]]] := finite_independent_span t.
pose U := finite_span_vect he.
pose j := subspace_inclusion (finite_span_subspace e).
have hj : injective j := @subspace_val_injective R V (finite_span_subspace e).
pose hU := inner_product_linear_pullback hB hj.
pose u (i:'I_m) : U := @subspace_lift R V (finite_span_subspace e) (tnth t i) (hspan (tnth t i) (mem_tnth i t)).
pose tu : m.-tuple U := [tuple u i | i<m].
pose g : S_m U W m := S_m_dual j f.
have htu : symmetric_form_unit_tuple (inner_norm hU) tu.
  move=> i; rewrite /tu tnth_mktuple inner_pullback_norm.
  change (inner_norm hB (tnth t i)<=1); exact: ht.
have [x [hx hb]] := @finite_hilbert_vector_diagonal_dominates R U W
  (fun x y=>B (j x) (j y)) hU NW hW n (finite_span_basis e)
  (finite_span_basisP he) m g tu htu.
exists (j x); split.
- by rewrite -(@inner_pullback_norm R U V B hB j hj x).
- rewrite /g !S_m_dualE in hb.
  have htuE : map_tuple j tu=t.
    apply: eq_from_tnth=> i; rewrite tnth_map /tu tnth_mktuple; by [].
  have hdiag : map_tuple j [tuple x | i<m]=[tuple j x | i<m].
    by apply: eq_from_tnth=> i; rewrite tnth_map !tnth_mktuple.
  by rewrite htuE hdiag in hb.
Qed.
