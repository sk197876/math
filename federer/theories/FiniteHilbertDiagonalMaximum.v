(** Federer (1969), 1.10.5, p. 48: finite-dimensional scalar case of the
    Hilbert-input equality attributed to [H 1]. The proof selects a
    secondary maximizing tuple and proves all its entries equal using the
    local pair-replacement lemmas. It includes zero degree, the zero form
    and the zero-dimensional input space. Source context and context:
    HilbertBilinearMaximizers.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm LinearBasis SymmetricForms
  SymmetricFormWords SymmetricOperatorNormUP SymmetricOneFormPowers
  HilbertWordMaximum HilbertWordDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_hilbert_diagonal_maximum]: Federer
    1.10.5, p. 48, supporting attained diagonal maximum.
    In a finite-dimensional real inner-product space, a scalar symmetric
    form has a unit-ball vector whose diagonal value in absolute value
    bounds every value on a tuple of unit-ball vectors. *)
Theorem finite_hilbert_diagonal_maximum (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (f : S_m V R^o m) :
  exists x, inner_norm hB x<=1 /\ forall t : m.-tuple V,
    symmetric_form_unit_tuple (inner_norm hB) t ->
    `|f t|<=`|f [tuple x | i<m]|.
Proof.
case: m f=> [f|m f].
- exists 0; split; first by rewrite inner_norm0 ler01.
  move=> t ht; by rewrite (tuple0 t) (tuple0 [tuple (0:V) | i<0]).
- have [s [hs [hu [hmax hsecondary]]]] :=
    @finite_hilbert_word_secondary_maximum R V B hB m.+1 f n e he.
  have htuple t : symmetric_form_unit_tuple (inner_norm hB) t ->
    `|f t|<=`|sform_words f s|.
    move=> ht; rewrite -(sform_wordsE f t); apply: hmax; first exact: size_tuple.
    move=> v /tnthP[i ->]; exact: ht.
  case hz : (`|sform_words f s|==0).
  + exists 0; split; first by rewrite inner_norm0 ler01.
    move=> t ht; have hh := htuple t ht; move/eqP: hz=> hz.
    rewrite hz in hh; exact: le_trans hh (normr_ge0 _).
  + have hp : 0<`|sform_words f s| by rewrite lt_def hz normr_ge0.
    have hunit := @hilbert_positive_maximizer_unit_entries R V B hB m.+1 f s hs hu hp hmax.
    have hne : s!=[::] by rewrite -size_eq0 hs.
    have [x [hx hxs]] := @hilbert_secondary_word_diagonal R V B hB m.+1 f
      `|sform_words f s| hmax s hs hne hunit erefl hsecondary.
    exists x; split; first by rewrite hx.
    move=> t ht; have hh := htuple t ht.
    have hxseq : ([tuple x | i<m.+1] : seq V)=nseq m.+1 x.
      by change ([seq x | i<-enum 'I_m.+1]=nseq m.+1 x); rewrite constant_map_nseq size_enum_ord.
    rewrite -(sform_wordsE f [tuple x | i<m.+1]) hxseq -hxs; exact hh.
Qed.
