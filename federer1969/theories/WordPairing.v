(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import DualExterior.
From Federer Require Import AlgebraWordLaws SharedIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, trace contraction: evaluate products of dual
    covectors on products of basis vectors, before summing in kappa. *)
Section WordPairing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
(** Source for [omega_word]: Federer (1969), 1.4.5, pp. 20-21, last display
    of p. 20 and its hypotheses at the top of p. 21. In words: Multiplying a
    degree-m diagonal tensor by Gamma of the identity on the j-th exterior
    power multiplies its trace by binomial(n-m,j), for 0<=j<=n-m. Definition
    or construction used to formalise this passage. The local LaTeX erratum
    (May 1987), p. 1, entry for book p. 20 line 32, corrects the identity to
    the identity on the j-th exterior power. *)
Definition omega_word (s : seq 'I_n) :=
  Omega h2 V (exterior_word [seq dual_basis he i | i <- s]).
(** Source for [omega_wordE]: Federer (1969), 1.4.5, pp. 20-21, last display
    of p. 20 and its hypotheses at the top of p. 21. In words: Multiplying a
    degree-m diagonal tensor by Gamma of the identity on the j-th exterior
    power multiplies its trace by binomial(n-m,j), for 0<=j<=n-m. Supporting
    lemma for this passage; not separately stated in the book. The local
    LaTeX erratum (May 1987), p. 1, entry for book p. 20 line 32, corrects
    the identity to the identity on the j-th exterior power. *)
Lemma omega_wordE m (s : m.-tuple 'I_n) : omega_word s =
  one_forms_product h2 (scalar_bilinear K) (1 : K^o) (fun i => omega (tnth s i)).
Proof.
rewrite /omega_word /Omega Omega_W_word /one_forms_product.
rewrite (map_comp (fun i => form_include (omega i)) (tnth s)) map_tnth_enum.
by rewrite -map_comp.
Qed.
(** Source for [omega_word_permutations]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma omega_word_permutations m (s t : m.-tuple 'I_n) :
  omega_word s (exterior_word [seq e i | i <- t]) =
  \sum_(sigma : 'S_m) FedererPermutation.index K sigma *:
    (if all (fun i => tnth s i == tnth t (sigma i)) (enum 'I_m) then 1 else 0 : K^o).
Proof.
rewrite omega_wordE.
change (one_forms_product h2 (scalar_bilinear K) (1 : K^o)
  (fun i => omega (tnth s i)) (exterior_word [tuple of map e t]) =
  \sum_(sigma : 'S_m) FedererPermutation.index K sigma *:
    (if all (fun i => tnth s i == tnth t (sigma i)) (enum 'I_m) then 1 else 0 : K^o)).
rewrite -one_forms_wedgeE (one_forms_wedge_permutations h2 (scalar_bilinear K) (@mulr1 K)).
apply: eq_bigr => sigma _; congr (_ *: _).
transitivity (foldr (fun x y : K => x*y) 1
  [seq if tnth s i == tnth t (sigma i) then 1 else 0 | i <- enum 'I_m]).
- congr (foldr _ _ _); apply: eq_map => i.
  by rewrite tnth_map one_formE dual_basisE eq_sym.
- exact: scalar_delta_product.
Qed.
(** Source for [omega_word_nonuniq]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma omega_word_nonuniq s : ~~ uniq s -> omega_word s = 0.
Proof. move=> hs; by rewrite /omega_word (exterior_word_map_nonuniq _ hs) linear0. Qed.
(** Source for [omega_word_shared]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma omega_word_shared m j (lambda mu : Lambda n m) (kappa : Lambda n j) :
  omega_word (val lambda ++ val kappa)
    (exterior_word [seq e i | i <- val mu ++ val kappa]) =
  if (lambda == mu) && uniq (val lambda ++ val kappa) then 1 else 0.
Proof.
case hu : (uniq (val lambda ++ val kappa)); last first.
- rewrite (omega_word_nonuniq (negbT hu)) andbF; exact: hom_finite_zeroE.
change (omega_word (cat_tuple (val lambda) (val kappa))
  (exterior_word [seq e i | i <- cat_tuple (val mu) (val kappa)]) =
  if (lambda == mu) && true then 1 else 0).
rewrite omega_word_permutations andbT.
under eq_bigr do rewrite (@Lambda_shared_delta n m j lambda mu kappa _ hu).
case hm : (lambda == mu).
- rewrite (bigD1 1%g) //= eqxx (index_one h2) scale1r.
  have hz : (\sum_(sigma : 'S_(m+j) | sigma != 1%g)
    FedererPermutation.index K sigma *: (if sigma == 1%g then 1 else 0 : K^o)) = 0.
    apply: big1 => sigma hs; by rewrite (negbTE hs) scaler0.
  by rewrite hz addr0.
- apply: big1 => sigma _; exact: scaler0.
Qed.
End WordPairing.
