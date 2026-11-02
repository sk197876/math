(** Federer (1969), 3.1.24, p. 239: the
    outer-linear term in the normalized composition coefficient
    contains exactly the highest inner coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices CompositionLinearIndex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_degree_one_factorial]: alpha! is
    one for the unique outer-linear term in S(p), supporting
    the inverse formula in Federer 3.1.24, p. 239. *)
Lemma composition_degree_one_factorial k p (a:composition_indices k p) :
  symmetric_multi_degree (composition_indices_unbound a)= 1%N ->
  symmetric_multi_factorial (composition_indices_unbound a)= 1%N.
Proof.
move=>hd; have [i [hi [hai hz]]]:=composition_degree_one_support hd.
rewrite /symmetric_multi_factorial; apply:big1=>j _.
case hji:(j==i).
- have he:j= i:=eqP hji; by rewrite he hai.
- have hj:j!=i by rewrite hji.
  by rewrite (hz j hj).
Qed.

(** Source for [composition_degree_one_scalar_monomial]: the
    normalized monomial of the outer-linear composition term
    equals lambda_p, supporting the inverse recurrence in
    Federer 3.1.24, p. 239. *)
Lemma composition_degree_one_scalar_monomial (K:fieldType) k p
    (a:composition_indices k p) (lambda:nat->K) :
  symmetric_multi_degree (composition_indices_unbound a)= 1%N ->
  symmetric_scalar_monomial (fun i:'I_k=>lambda (val i).+1) (composition_indices_unbound a)=lambda p.
Proof.
move=>hd; have [i [hi [hai hz]]]:=composition_degree_one_support hd.
rewrite /symmetric_scalar_monomial (bigD1 i) // hai expr1 hi.
have he:(\prod_(j<k | j!=i) lambda (val j).+1^+(composition_indices_unbound a j))= 1.
  apply:big1=>j hj; by rewrite (hz j hj) expr0.
rewrite he; change (lambda p*(1:K)= lambda p); exact:mulr1.
Qed.
