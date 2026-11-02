(** Federer (1969), 1.10.6, p. 49: there are m!/alpha! functions with
    prescribed fibre cardinalities alpha. The proof below extracts a
    monomial coefficient from the already proved multinomial theorem of
    1.9.3, p. 42, instead of repeating a permutation quotient count. The
    occurrence coordinate ranges through n, correcting the printed m in
    Federer's fibre condition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom SymmetricAlgebra SymmetricGrading SymmetricMultiIndices
  SymmetricIndexBounds SymmetricMonomials SymmetricDividedMonomials SymmetricMultinomial
  SymmetricWordExpansion SymmetricWordFibres SymmetricMonomialCoordinates
  SymmetricCoordinateDualBasis SymmetricOneFormPowers LinearBasis FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_sum_vector_power_words]: Federer 1.10.6,
    p. 49, supporting counting expansion: distributing m copies
    of a sum of n vectors gives one summand for every function
    from the argument positions to the basis indices. *)
Lemma symmetric_sum_vector_power_words (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) m :
  symmetric_vector_power (\sum_i e i) m =
    \sum_(s : {ffun 'I_m -> 'I_n})
      symmetric_monomial e (symmetric_indices_unbound (symmetric_function_occurrences s)).
Proof.
have hh := @symmetric_word_expansion K V (Finite.clone 'I_m _) (Finite.clone 'I_n _)
  (fun _ _ => 1) e.
have hsum (i : 'I_m) : (\sum_j (1:K) *: e j) = \sum_j e j.
  by under eq_bigr do rewrite scale1r.
have hmap : [seq \sum_j (1:K) *: e j | i <- enum 'I_m] =
    nseq m (\sum_j e j).
  rewrite (eq_map (fun i => hsum i)) constant_map_nseq size_enum_ord.
  by [].
rewrite hmap in hh.
rewrite /symmetric_vector_power hh; apply: eq_bigr=> s _.
rewrite prodr_const expr1n scale1r symmetric_function_occurrencesE.
rewrite -(@symmetric_word_occurrence_monomial K V n e
  [seq s i | i <- enum 'I_m]) map_comp.
by [].
Qed.

(** Source for [symmetric_fibre_cardinality_scalar]: Federer 1.10.6,
    p. 49, the prescribed-fibre count as a real scalar: m!
    divided by alpha!. Its proof extracts the alpha coefficient in
    the two expansions of the same power. *)
Theorem symmetric_fibre_cardinality_scalar (R : rcfType) n m
    (a : symmetric_indices n m) :
  (#|[pred s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a]|)%:R =
    ((m`!)%:R : R) * ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R)^-1.
Proof.
pose e := @coordinate_basis R n.
pose he := coordinate_basisP R n.
pose l := symmetric_monomial_coordinate he (symmetric_indices_unbound a).
have hm := @symmetric_multinomial R (@pchar_num R) (coordinate_space R n) n e m.
have hv := congr1 (fun z => l z) hm.
rewrite /symmetric_divided_vector_power linearZ linear_sum in hv.
change (((m`!)%:R : R)^-1 * l (symmetric_vector_power (\sum_i e i) m) =
  \sum_(b : symmetric_indices n m) l (symmetric_divided_monomial e (symmetric_indices_unbound b))) in hv.
rewrite symmetric_sum_vector_power_words linear_sum in hv.
have hl (b : symmetric_indices n m) : l (symmetric_monomial e (symmetric_indices_unbound b)) =
    if b == a then 1 else 0.
  rewrite /l symmetric_monomial_coordinateE.
  by rewrite (inj_eq (@symmetric_indices_unbound_injective n m)).
have hs : (\sum_(s : {ffun 'I_m -> 'I_n})
    l (symmetric_monomial e (symmetric_indices_unbound (symmetric_function_occurrences s)))) =
    (#|[pred s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a]|)%:R.
  under eq_bigr do rewrite hl.
  by rewrite -sumr_const -big_mkcond.
have hr : (\sum_(b : symmetric_indices n m) l (symmetric_divided_monomial e (symmetric_indices_unbound b))) =
    ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R)^-1.
  have hvb (b : symmetric_indices n m) :
      l (symmetric_divided_monomial e (symmetric_indices_unbound b)) =
      ((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : R)^-1 *
        (if b == a then 1 else 0).
    rewrite /symmetric_divided_monomial linearZ.
    change (((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : R)^-1 *
      l (symmetric_monomial e (symmetric_indices_unbound b)) =
      ((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : R)^-1 *
        (if b == a then 1 else 0)).
    by rewrite hl.
  rewrite (bigD1 a) // hvb eqxx mulr1.
  have hz : (\sum_(b | b != a) l (symmetric_divided_monomial e (symmetric_indices_unbound b))) = 0.
    apply: big1=> b hb; by rewrite hvb (negbTE hb) mulr0.
  change (((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R)^-1 +
    (\sum_(b | b != a) l (symmetric_divided_monomial e (symmetric_indices_unbound b))) =
    ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R)^-1).
  by rewrite hz addr0.
rewrite hs hr in hv.
have hf : ((m`!)%:R:R) != 0 by rewrite pnatr_eq0 -lt0n fact_gt0.
rewrite -hv mulrA mulfV // mul1r.
by [].
Qed.

(** Source for [symmetric_fibre_cardinality_factorial]: Federer 1.10.6,
    p. 49, integral form of the prescribed-fibre count: multiplying
    the number of functions by alpha! gives m!. This also proves
    divisibility before using natural-number division. *)
Theorem symmetric_fibre_cardinality_factorial (R : rcfType) n m
    (a : symmetric_indices n m) :
  (#|[pred s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a]| *
    symmetric_multi_factorial (symmetric_indices_unbound a) = m`!)%N.
Proof.
have h := symmetric_fibre_cardinality_scalar R a.
have ha := @symmetric_multi_factorial_nonzero R (@pchar_num R) n
  (symmetric_indices_unbound a).
have he : ((#|[pred s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a]| *
    symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R) = (m`!)%:R.
  by rewrite natrM h -mulrA mulVf // mulr1.
by move/eqP: he; rewrite eqr_nat=> /eqP.
Qed.

(** Source for [symmetric_fibre_cardinality]: Federer 1.10.6,
    p. 49, the printed count m!/alpha! as an equality of
    natural numbers. The occurrence coordinate is indexed through n,
    correcting the printed m. Empty functions and zero variables are included. *)
Theorem symmetric_fibre_cardinality (R : rcfType) n m
    (a : symmetric_indices n m) :
  #|[pred s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a]| =
    (m`! %/ symmetric_multi_factorial (symmetric_indices_unbound a))%N.
Proof.
have ha : (0 < symmetric_multi_factorial (symmetric_indices_unbound a))%N.
  have hh := @symmetric_multi_factorial_nonzero R (@pchar_num R) n
    (symmetric_indices_unbound a).
  by move: hh; rewrite pnatr_eq0 -lt0n.
by rewrite -(symmetric_fibre_cardinality_factorial R a) mulnK.
Qed.
