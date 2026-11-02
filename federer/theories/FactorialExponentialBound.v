(** Federer (1969), 3.1.24, p. 238: supporting the
    exponential factorial bound used with polarization. The printed
    constant e is replaced by 4; existence of an analytic bound
    is unchanged. The proof uses the scalar multinomial theorem
    and the count of multiindices proved in 1.9.2–3. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarDividedMultinomial SymmetricMultiIndices
  SymmetricIndexBounds SymmetricIndexCardinality SymmetricMonomials SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [binomial_power_two_bound]: supporting the
    factorial estimate in Federer 3.1.24, p. 238.
    Every binomial coefficient is at most the sum 2^n
    of its row; Pascal induction includes both boundary cases. *)
Lemma binomial_power_two_bound n k : ('C(n,k)<=2^n)%N.
Proof.
elim: n k=>[k|n ih [|k]].
- case:k=>[|k]; by rewrite bin0n /=.
- rewrite bin0; exact: expn_gt0.
- rewrite binS expnS mul2n -addnn; exact: leq_add (ih _) (ih _).
Qed.

(** Source for [factorial_exponential_bound]: supporting the
    implication (4) to (1) in Federer 3.1.24,
    p. 238. The scalar multinomial identity bounds n^n/n!
    by the number of n-variable degree-n multiindices, hence
    by 4^n. This deliberately weaker constant avoids importing
    an exponential or Stirling estimate. Degree zero is included. *)
Lemma factorial_exponential_bound (R:realType) n :
  (n%:R:R)^+n <= (4:R)^+n * (n`!)%:R.
Proof.
case:n=>[|k]; first by rewrite expr0 fact0 mulr1.
have hf:0<(((k.+1)`!)%:R:R) by rewrite ltr0n fact_gt0.
rewrite -ler_pdivrMr //.
have hm:=@scalar_divided_multinomial R (@pchar_num R) k.+1 (fun _=>1) k.+1.
rewrite sumr_const card_ord in hm.
rewrite -hm.
apply: le_trans (_ : (#|{:symmetric_indices k.+1 k.+1}|%:R:R) <= (4:R)^+k.+1).
- have he:(#|{:symmetric_indices k.+1 k.+1}|%:R:R)=
      \sum_(a:symmetric_indices k.+1 k.+1) (1:R).
    by rewrite sumr_const.
  rewrite he; apply: ler_sum=>a _.
  rewrite /symmetric_scalar_monomial.
  under eq_bigr do rewrite expr1n.
  rewrite prodr_const expr1n mul1r.
  have hp:(0<symmetric_multi_factorial (symmetric_indices_unbound a))%N.
    rewrite /symmetric_multi_factorial; apply/prodn_gt0; by move=>i; rewrite fact_gt0.
  rewrite -div1r ler_pdivrMr; last by rewrite ltr0n.
  by rewrite mul1r ler1n.
- rewrite card_symmetric_indices -natrX ler_nat.
  apply: leq_trans (binomial_power_two_bound _ _) _.
  rewrite -[4%N]/(2^2)%N -expnM.
  apply: leq_pexp2l; first by [].
  by rewrite mul2n -addnn leq_add2l.
Qed.
