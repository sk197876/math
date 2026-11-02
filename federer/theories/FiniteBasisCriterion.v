(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FiniteIndependence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: a finite independent family of the full dimension
    is a basis. The adapter below relates finite sums to the project's
    basis predicate, and uses MathComp's abstract vector-space dimension. *)
Section FiniteCoefficients.
Variable K : fieldType.
Variable I : finType.
Local Notation F := (GRing.Lmodule.clone K (free_vector K (Choice.clone I _)) _).
(** Source for [finite_coeff_vector]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Definition or construction used to formalise
    this passage. *)
Definition finite_coeff_vector (c : I -> K) : F := \sum_i c i *: delta K i.
(** Source for [finite_coeff_vectorE]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_coeff_vectorE c j : finite_coeff_vector c j = c j.
Proof.
change (free_eval j (\sum_i c i *: delta K i) = c j).
rewrite linear_sum.
change ((\sum_i free_eval j (c i *: delta K i)) = c j).
under eq_bigr do rewrite (linZ (linearP (free_eval j))).
change ((\sum_i c i * delta K i j) = c j).
under eq_bigr do rewrite deltaE.
rewrite (bigD1 j) //= eqxx mulr1.
have hz : (\sum_(i | i != j) c i * (if j == i then 1 else 0)) = 0.
  apply: big1 => i hi; by rewrite eq_sym (negbTE hi) mulr0.
by rewrite hz addr0.
Qed.
(** Source for [finite_coeff_vectorK]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_coeff_vectorK (f : F) : finite_coeff_vector (fun i => f i) = f.
Proof. by apply/fsfunP=> i; rewrite finite_coeff_vectorE. Qed.
Variable V : lmodType K.
Variable e : I -> V.
(** Source for [basis_synthesis_finite]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_synthesis_finite c : basis_synthesis e (finite_coeff_vector c) = \sum_i c i *: e i.
Proof.
rewrite /finite_coeff_vector linear_sum.
apply: eq_bigr => i _; exact (eq_trans (linZ (linearP (basis_synthesis e)) (c i) (delta K i))
  (congr1 (fun v : V => c i *: v) (basis_synthesisE e i))).
Qed.
(** Source for [basis_synthesis_finiteE]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_synthesis_finiteE (f : F) : basis_synthesis e f = \sum_i f i *: e i.
Proof. by rewrite -{1}(finite_coeff_vectorK f) basis_synthesis_finite. Qed.
(** Source for [finite_synthesis_injective]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_synthesis_injective : finite_independent e -> injective (basis_synthesis e).
Proof.
move=> he c d h.
have hz : basis_synthesis e (c-d) = 0 by rewrite linearB h subrr.
rewrite basis_synthesis_finiteE in hz.
have hc := he (fun i => (c-d) i) hz.
apply/fsfunP=> i; have hi := hc i.
change ((c-d) i = 0) in hi.
rewrite free_addE free_oppE in hi; exact (subr0_eq hi).
Qed.
(** Source for [finite_basis_criterion]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem finite_basis_criterion : finite_independent e ->
  (forall v, exists c : I -> K, v = \sum_i c i *: e i) -> is_basis e.
Proof.
move=> hi hs; apply/basisP; split; first exact: finite_synthesis_injective.
move=> v; have [c hc] := hs v; exists (finite_coeff_vector c).
by rewrite basis_synthesis_finite -hc.
Qed.
End FiniteCoefficients.

(** Source for [finite_independent_basis]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem finite_independent_basis (K : fieldType) (V : vectType K) n (e : 'I_n -> V) :
  dim V = n -> finite_independent e -> is_basis e.
Proof.
move=> hd hi.
pose t : n.-tuple V := [tuple e i | i < n].
have ht (i : 'I_n) : t`_i = e i := nth_mktuple e (0 : V) i.
have hsum (c : 'I_n -> K) : (\sum_i c i *: t`_i) = \sum_i c i *: e i.
  apply: eq_bigr => i _; by rewrite ht.
have hf : free t.
  apply/freeP=> c hc; apply: hi; by rewrite -(hsum c).
have hb : basis_of {:V} t.
  by rewrite basisEfree hf subvf dimvf hd size_tuple leqnn.
apply: finite_basis_criterion hi _ => v.
exists (fun i => coord t i v).
have he := coord_basis hb (memvf v).
by rewrite hsum in he.
Qed.

(** Source for [finite_independent_reindex]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_independent_reindex (K : fieldType) (I J : finType) (V : lmodType K)
    (e : J -> V) (f : I -> J) (g : J -> I) :
  cancel f g -> cancel g f -> finite_independent e -> finite_independent (fun i => e (f i)).
Proof.
move=> fg gf he c hc i.
have hb : bijective f by exists g.
have hz : \sum_j c (g j) *: e j = 0.
  rewrite (reindex f (onW_bij _ hb)).
  under eq_bigr do rewrite fg.
  exact: hc.
have hi := he (fun j => c (g j)) hz (f i); by rewrite fg in hi.
Qed.
(** Source for [finite_independent_basis_card]: Federer (1969), 1.6.1, p.
    23, dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem finite_independent_basis_card (K : fieldType) (V : vectType K)
    (I : finType) (e : I -> V) : dim V = #|I| -> finite_independent e -> is_basis e.
Proof.
move=> hd hi.
have hf : finite_independent (fun i : 'I_(#|I|) => e (enum_val i)).
  exact: finite_independent_reindex (@enum_valK I) (@enum_rankK I) hi.
have hb := finite_independent_basis hd hf.
have h := @basis_reindex K (Choice.clone 'I_(#|I|) _) (Choice.clone I _) V
  (fun i => e (enum_val i)) hb enum_val enum_rank (@enum_valK I) (@enum_rankK I).
apply: basis_congr h => i; by rewrite enum_rankK.
Qed.
