(** Federer (1969), 3.1.11, pp. 221–222:
    an order-k asymptotic comparison determines the
    first k+1 coefficients of any finite polynomial.
    Terms of higher degree need not be discarded
    in advance when multiplying or composing jets. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP PolynomialCoefficientUniqueness
  NormedCurveDerivativeUP NormLittleOPower VectorPolynomialNearZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [vector_polynomial_little_o_initial_coefficients_zero]:
    the coefficient-comparison argument behind
    the product and composition formulas in
    Federer 3.1.11, p. 222.
    Only coefficients of degree at most k
    vanish; the polynomial's full degree may
    be larger than k. *)
Theorem vector_polynomial_little_o_initial_coefficients_zero (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N) k (s : seq Y) :
  norm_little_o_power N (coefficient_polynomial_value s) k ->
  all (pred1 0) (take k.+1 s).
Proof.
elim:k s=>[s ho|k ih s ho].
- case:s ho=>[//|c s] ho.
  have hc := punctured_norm_limit_unique hN
    (vector_polynomial_zero_limit hN c s) (norm_little_o_power_zero_limit ho).
  by rewrite /= take0 hc eqxx.
- case:s ho=>[//|c s] ho.
  have hc := punctured_norm_limit_unique hN
    (vector_polynomial_zero_limit hN c s) (norm_little_o_power_zero_limit ho).
  rewrite /= hc eqxx /=; apply: ih.
  move=>e he; have [d [hd hb]] := ho e he.
  exists d; split=> // t ht.
  have hh := hb t ht.
  change (is_true (N (c+t*:coefficient_polynomial_value s t)<=e*`|t|^+k.+1)) in hh.
  rewrite hc add0r (real_seminorm_scale hN.1) exprS in hh.
  have heq : e*(`|t|*`|t|^+k)=`|t|*(e*`|t|^+k) by ring.
  rewrite heq in hh; by move:hh; rewrite (ler_pM2l (andP ht).1).
Qed.

(** Source for [finite_power_little_o_initial_coefficients_zero]:
    finite-sum form of the same truncated
    uniqueness, supporting Federer 3.1.11,
    pp. 221–222. *)
Theorem finite_power_little_o_initial_coefficients_zero (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N)
    k M (c : nat->Y) :
  norm_little_o_power N (fun t=>\sum_(i<M) t^+i*:c i) k ->
  forall i, (i<=k)%N -> (i<M)%N -> c i= 0.
Proof.
move=>ho.
pose s := [seq c i | i<-iota 0 M].
have he t : coefficient_polynomial_value s t=\sum_(i<M) t^+i*:c i.
  rewrite coefficient_polynomial_sum /s size_map size_iota.
  apply: eq_bigr=>i _.
  by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
have hsO : norm_little_o_power N (coefficient_polynomial_value s) k.
  move=>e heps; have [d [hd hb]] := ho e heps.
  exists d; split=> // t ht; rewrite he; exact: hb.
have /allP hz := vector_polynomial_little_o_initial_coefficients_zero hN hsO.
move=>i hik hiM.
have his : (i<size (take k.+1 s))%N.
  by rewrite size_take size_map size_iota ltn_min ltnS hik hiM.
have hin := mem_nth (0:Y) his.
have hec : nth 0 (take k.+1 s) i=c i.
  rewrite nth_take; last by rewrite ltnS.
  by rewrite /s (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite hec in hin; exact: eqP (hz _ hin).
Qed.

(** Source for [finite_power_initial_asymptotic_coefficients_unique]:
    two finite expansions of a function
    to order k have the same
    coefficients through degree k, Federer
    3.1.11, pp. 221–222.
    No bound on their full degree is required. *)
Theorem finite_power_initial_asymptotic_coefficients_unique (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N)
    k M (f : R->Y) (c d : nat->Y) :
  norm_little_o_power N (fun t=>f t-\sum_(i<M) t^+i*:c i) k ->
  norm_little_o_power N (fun t=>f t-\sum_(i<M) t^+i*:d i) k ->
  forall i, (i<=k)%N -> (i<M)%N -> c i=d i.
Proof.
move=>hc hd.
have hh := norm_little_o_power_add hN hd (norm_little_o_power_negate hN hc).
have he t :
    (f t-\sum_(i<M) t^+i*:d i) + -(f t-\sum_(i<M) t^+i*:c i)=
    \sum_(i<M) t^+i*:(c i-d i).
  rewrite opprB [(_-f t)]addrC addrACA subrr add0r addrC -sumrB.
  apply: eq_bigr=>i _; by rewrite scalerBr.
have hp : norm_little_o_power N (fun t=>\sum_(i<M) t^+i*:(c i-d i)) k.
  move=>e heps; have [r [hr hb]] := hh e heps.
  exists r; split=> // t ht; rewrite -(he t); exact: hb.
move=>i hi hiM.
have hz := @finite_power_little_o_initial_coefficients_zero R Y N hN k M (fun j=>c j-d j) hp i hi hiM.
by move/eqP:hz; rewrite subr_eq0=>/eqP.
Qed.
