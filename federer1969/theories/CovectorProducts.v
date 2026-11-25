(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import OneFormProducts ScalarCoefficients LambdaPermutation
  FiniteIndependence Biorthogonal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: omega_lambda is the alternating product of the
    one-covectors in the increasing order specified by lambda. *)
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> A_m V K^o 1.
(** Source for [omega_lambda]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition omega_lambda m (lambda : Lambda n m) : A_m V K^o m :=
  one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
    (fun i => omega (tnth (val lambda) i)).
(** Source for [omega_lambda_include]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma omega_lambda_include m (lambda : Lambda n m) :
  form_include (omega_lambda lambda) = foldr (alternating_wedge h2 (scalar_bilinear K))
    (coefficient_form V (1 : K^o)) [seq form_include (omega i) | i <- val lambda].
Proof.
rewrite /omega_lambda (one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)) /one_forms_product.
by rewrite (map_comp (fun i => form_include (omega i)) (tnth (val lambda))) map_tnth_enum.
Qed.
End Products.

(** Source for [pairing_e_lambda]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma pairing_e_lambda (K : fieldType) (I : choiceType) (V W : lmodType K)
    (e : I -> V) m (t : m.-tuple I) (a : A_m V W m) :
  pairing (e_lambda e t) a = a [tuple of map e t].
Proof.
rewrite /pairing form_to_homE e_lambdaE form_extensionE.
exact (@form_wordsE K V W m a [tuple of map e t]).
Qed.

Section Pairing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m : nat.
Variable omega : 'I_n -> A_m V K^o 1.
Variable e : 'I_n -> V.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [omega_lambda_permutation_values]: Federer (1969), 1.4.3, p.
    19, opening assertion and biorthogonal-vector argument. In words:
    Increasing products of a finite independent family of covectors are
    independent; evaluation on the corresponding products of biorthogonal
    vectors gives the Kronecker pairing. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma omega_lambda_permutation_values (lambda mu : Lambda n m) (sigma : 'S_m) :
  [seq omega (tnth (val lambda) i) [tuple tnth [tuple of map e (val mu)] (sigma i)]
    | i <- enum 'I_m] =
  [seq if tnth (val lambda) i == tnth (val mu) (sigma i) then 1 else 0 | i <- enum 'I_m].
Proof. apply: eq_map => i; by rewrite tnth_map hdual. Qed.
(** Source for [pairing_e_omega]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem pairing_e_omega (lambda mu : Lambda n m) :
  pairing (e_lambda e (val mu)) (omega_lambda h2 omega lambda) =
    if lambda == mu then 1 else 0.
Proof.
rewrite pairing_e_lambda /omega_lambda (one_forms_wedge_permutations h2 (scalar_bilinear K) (@mulr1 K)).
under eq_bigr do rewrite omega_lambda_permutation_values scalar_delta_product Lambda_permutation_delta.
case he : (lambda == mu).
- rewrite (bigD1 1%g) //= eqxx (index_one h2) scale1r.
  have hz : (\sum_(sigma : 'S_m | sigma != 1%g) FedererPermutation.index K sigma *:
      (if sigma == 1%g then 1 else 0 : K^o)) = 0.
    apply: big1 => sigma hs; by rewrite (negbTE hs) scaler0.
  by rewrite hz addr0.
- apply: big1 => sigma _; exact: scaler0.
Qed.
End Pairing.
