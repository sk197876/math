(** Federer (1969), 3.1.11, p. 222: the multinomial
    calculation in the composition of jets, using the symmetric
    algebra of 1.9.3. The weighted degree and ordinary degree
    are kept distinct throughout the calculation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom SymmetricAlgebra SymmetricMultiIndices
  SymmetricIndexBounds SymmetricMonomials SymmetricDividedMonomials
  SymmetricMultinomial CompositionMultiIndices CompositionIndexSummation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_scalar_monomial]: the scalar
    power associated with alpha is t to the weighted degree
    sum_i i alpha_i, Federer 3.1.11, p. 222. *)
Lemma composition_scalar_monomial (K : fieldType) k
    (a : symmetric_multi_index k) (t : K) :
  symmetric_scalar_monomial (fun i : 'I_k=>t^+(val i).+1) a=
    t^+(composition_multi_weight a).
Proof.
rewrite /symmetric_scalar_monomial /composition_multi_weight.
under eq_bigr do rewrite -exprM.
by rewrite expr_sum.
Qed.

Section CompositionMultinomial.
Variable K : fieldType.
Hypothesis h0 : [pchar K]=i pred0.
Variables Y T : lmodType K.
Variable k : nat.
Variable c : 'I_k->Y.
Variable L : nat->Hom (symmetric_space Y) T.

(** Source for [composition_multinomial_term]: one coefficient
    in the last double sum on p. 222 of Federer 3.1.11.
    The argument c_i is already divided by i!, whereas the
    remaining factor is precisely 1/alpha!. *)
Definition composition_multinomial_term (a : symmetric_multi_index k) : T :=
  ((symmetric_multi_factorial a)%:R)^-1 *:
    L (symmetric_multi_degree a) (symmetric_monomial c a).

(** Source for [composition_multinomial_expansion]: the first
    multinomial expansion in the composition calculation of Federer
    3.1.11, p. 222. The degree-zero term is included. *)
Theorem composition_multinomial_expansion t :
  \sum_(j<k.+1) L j
    (symmetric_divided_vector_power (\sum_(i<k) t^+(val i).+1*:c i) j)=
  \sum_(a : composition_expansion_indices k)
    t^+(composition_multi_weight (composition_expansion_unbound a))*:
      composition_multinomial_term (composition_expansion_unbound a).
Proof.
transitivity (\sum_(j<k.+1) \sum_(a : symmetric_indices k j)
  t^+(composition_multi_weight (symmetric_indices_unbound a))*:
    composition_multinomial_term (symmetric_indices_unbound a)).
- apply: eq_bigr=>j _.
  rewrite (symmetric_weighted_multinomial h0) linear_sum.
  apply: eq_bigr=>a _.
  rewrite linearZ composition_scalar_monomial /composition_multinomial_term
    symmetric_indices_unbound_degree /symmetric_divided_monomial linearZ.
  reflexivity.
- rewrite sig_big_dep /=; apply: eq_bigr=>[[j a]] _; by [].
Qed.

(** Source for [composition_weight_coefficient]: the terms
    collected at weighted degree p in the composition expansion,
    Federer 3.1.11, p. 222. *)
Definition composition_weight_coefficient p : T :=
  \sum_(a : composition_expansion_indices k |
    composition_multi_weight (composition_expansion_unbound a)==p)
    composition_multinomial_term (composition_expansion_unbound a).

(** Source for [composition_weight_coefficient_formula]: for
    p<=k the coefficient is the single sum over S(p) in
    Federer 3.1.11, p. 222, with no extraneous terms. *)
Theorem composition_weight_coefficient_formula p :
  (p<=k)%N -> composition_weight_coefficient p=
    \sum_(a : composition_indices k p)
      composition_multinomial_term (composition_indices_unbound a).
Proof. exact: composition_expansion_weight_sum. Qed.

(** Source for [composition_multinomial_collected]: the last
    sum, over weighted degrees at most k squared, in the
    composition-of-jets calculation, Federer 3.1.11, p. 222. *)
Theorem composition_multinomial_collected t :
  \sum_(j<k.+1) L j
    (symmetric_divided_vector_power (\sum_(i<k) t^+(val i).+1*:c i) j)=
  \sum_(p<(k*k).+1) t^+p*:composition_weight_coefficient p.
Proof.
rewrite composition_multinomial_expansion.
have hw (a : composition_expansion_indices k) :
    (composition_multi_weight (composition_expansion_unbound a)<(k*k).+1)%N.
  rewrite ltnS; exact: composition_expansion_weight_bound.
pose w (a : composition_expansion_indices k) : 'I_(k*k).+1 := Ordinal (hw a).
rewrite (partition_big w predT) //=.
apply: eq_bigr=>p _.
rewrite /composition_weight_coefficient scaler_sumr.
apply: eq_big.
- move=>a; by rewrite /w /= -val_eqE.
- move=>a /eqP ha.
  have he : composition_multi_weight (composition_expansion_unbound a)=val p :=
    congr1 val ha.
  by rewrite he.
Qed.
End CompositionMultinomial.
