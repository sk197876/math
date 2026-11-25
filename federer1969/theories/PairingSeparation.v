(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import DualExterior LinearRetraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: scalar linear functionals separate vectors. This
    justifies the uniqueness in the second characteristic condition,
    including in infinite dimension. *)
Section Separation.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [scalar_line]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition scalar_line (v : V) (a : K^o) : V := a *: v.
(** Source for [scalar_line_linear]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma scalar_line_linear v : linear (scalar_line v).
Proof. by move=> a b c; rewrite /scalar_line scalerDl scalerA. Qed.
HB.instance Definition _ v := GRing.isLinear.Build K K^o V *:%R
  (scalar_line v) (scalar_line_linear v).
(** Source for [scalar_line_injective]: Federer (1969), 1.5.1, p. 21,
    opening two bilinear maps and characteristic pairing conditions. In
    words: Right interior multiplication is characterised by adjoining the
    vector on the right inside the pairing; left interior multiplication is
    characterised by multiplying the covector on the left. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma scalar_line_injective v : v != 0 -> injective (scalar_line v).
Proof.
move=> hv a b hab; rewrite /scalar_line in hab; apply/eqP; rewrite -subr_eq0.
have hz : (a-b) *: v = 0 by rewrite scalerBl hab subrr.
by move/eqP: hz; rewrite scaler_eq0 (negPf hv) orbF.
Qed.
(** Source for [nonzero_functional]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonzero_functional v : v != 0 -> exists f : Hom V K^o, f v = 1.
Proof.
move=> hv; pose f := extension_along (scalar_line_injective hv) (linear_id K^o).
exists (hom_of_linear f).
have h := @extension_alongE K K^o V K^o (GRing.Linear.clone _ _ _ _ (scalar_line v) _)
  (scalar_line_injective hv) (linear_id K^o) 1.
change (f (1 *: v) = 1) in h.
by move: h; rewrite scale1r.
Qed.
(** Source for [linear_functionals_separate]: Federer (1969), 1.5.1, p. 21,
    opening two bilinear maps and characteristic pairing conditions. In
    words: Right interior multiplication is characterised by adjoining the
    vector on the right inside the pairing; left interior multiplication is
    characterised by multiplying the covector on the left. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem linear_functionals_separate (x y : V) :
  (forall f : Hom V K^o, f x = f y) -> x = y.
Proof.
move=> h; apply/eqP; rewrite -subr_eq0; apply/negPn/negP=> hxy.
have [f hf] := nonzero_functional hxy.
have hz : f (x-y) = 0.
  rewrite linearB; change (f x - f y = 0); by rewrite (h f) subrr.
by move: hf; rewrite hz => /esym/eqP; rewrite oner_eq0.
Qed.
End Separation.

(** Federer 1.5.1: the pairing with all (q-p)-covectors separates
    the actual (q-p)-vectors. *)
(** Source for [pairing_vectors_separate]: Federer (1969), 1.5.1, p. 21,
    opening two bilinear maps and characteristic pairing conditions. In
    words: Right interior multiplication is characterised by adjoining the
    vector on the right inside the pairing; left interior multiplication is
    characterised by multiplying the covector on the left. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem pairing_vectors_separate (K : fieldType) (V : lmodType K) m
  (x y : exterior_power V m) :
  (forall phi : A_m V K^o m, pairing x phi = pairing y phi) -> x = y.
Proof.
move=> h; apply: linear_functionals_separate => f.
move: (h (hom_to_form f)).
by rewrite /pairing !hom_to_formK.
Qed.
