(** Federer (1969), 1.7.5, pp. 31-32: gamma sends products of vectors to
    products of their polar covectors. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  AlgebraUP ExteriorAlgebra ExteriorGrading FiniteExteriorPowers
  AlternatingCoordinates AlternatingUnit AlternatingProduct ScalarCoefficients
  OneFormProducts CovectorProducts Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Products.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation gamma := (inner_exterior_extension h2 hB).

(** Source for [inner_exterior_word]: Federer 1.7.5,
    p. 31, the algebra extension sends a word of vectors to
    the alternating product of their polarities. *)
Lemma inner_exterior_word s : gamma (exterior_word s) =
  foldr (alternating_wedge h2 (scalar_bilinear R)) (coefficient_form V (1 : R^o))
    [seq form_include (inner_polarity hB v) | v <- s].
Proof.
elim: s => [|v s ih].
- rewrite exterior_word_nil; exact: algebra_map_one.
- rewrite exterior_word_cons /wedge algebra_map_mul.
  by rewrite /= inner_exterior_generator ih.
Qed.

(** Source for [inner_exterior_product_covectors]: Federer
    1.7.5, p. 31, gamma_m(v1 wedge ... wedge vm) is
    beta(v1) wedge ... wedge beta(vm). *)
Lemma inner_exterior_product_covectors m (e : 'I_m -> V) :
  inner_exterior_form h2 hB (e_lambda e (ord_tuple m)) =
    one_forms_wedge h2 (scalar_bilinear R) (1 : R^o)
      (fun i => inner_polarity hB (e i)).
Proof.
apply: (can_inj (@form_includeK R V R^o m)).
rewrite inner_exterior_form_include e_lambdaE inner_exterior_word
  (one_forms_wedge_include h2 (scalar_bilinear R) (@mulr1 R)) /one_forms_product.
by rewrite -map_comp.
Qed.

(** Source for [exterior_inner_product_permutations]: Federer
    1.7.5, pp. 31-32, the displayed permutation formula for
    the inner product of two simple m-vectors. *)
Theorem exterior_inner_product_permutations m (e f : 'I_m -> V) :
  exterior_inner_form h2 hB (e_lambda e (ord_tuple m)) (e_lambda f (ord_tuple m)) =
    \sum_(sigma : 'S_m) FedererPermutation.index R sigma *
      foldr ( *%R) 1 [seq B (e (sigma i)) (f i) | i <- enum 'I_m].
Proof.
rewrite /exterior_inner_form inner_exterior_product_covectors pairing_e_lambda
  (one_forms_wedge_permutations h2 (scalar_bilinear R) (@mulr1 R)).
apply: eq_bigr => sigma _; congr (_ * _); congr (foldr _ _ _).
apply: eq_map => i; by rewrite tnth_map tnth_ord_tuple inner_polarityE.
Qed.
End Products.
