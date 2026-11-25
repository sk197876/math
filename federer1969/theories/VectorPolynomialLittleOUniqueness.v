(** Federer (1969), 3.1.11, p. 221:
    a polynomial of degree at most k which
    is little-o of |t|^k has all coefficients
    zero. This is the scalar-line coefficient
    comparison used to identify higher differentials. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP PolynomialCoefficientUniqueness
  NormedCurveDerivativeUP NormLittleOPower VectorPolynomialNearZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [vector_polynomial_little_o_coefficients_zero]:
    the coefficient uniqueness behind the linewise
    corollary of Federer 3.1.11, p. 221.
    First the constant coefficient vanishes by
    continuity; division by nonzero t reduces
    both the degree and the remainder order. *)
Theorem vector_polynomial_little_o_coefficients_zero (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N) k (s : seq Y) :
  (size s<=k.+1)%N ->
  norm_little_o_power N (coefficient_polynomial_value s) k ->
  all (pred1 0) s.
Proof.
elim:k s=>[s hs ho|k ih s hs ho].
- case:s hs ho=>[//|c s] hs ho.
  have hc := punctured_norm_limit_unique hN
    (vector_polynomial_zero_limit hN c s) (norm_little_o_power_zero_limit ho).
  have hs0 : s=[::].
    apply/eqP; rewrite -size_eq0 -leqn0.
    by move:hs; rewrite /=.
  by rewrite hc hs0 /= eqxx.
- case:s hs ho=>[//|c s] hs ho.
  have hc := punctured_norm_limit_unique hN
    (vector_polynomial_zero_limit hN c s) (norm_little_o_power_zero_limit ho).
  rewrite hc /= eqxx /=.
  apply: ih; first by move:hs; rewrite /=.
  move=>e he; have [d [hd hb]] := ho e he.
  exists d; split=> // t ht.
  have hh := hb t ht.
  change (is_true (N (c+t*:coefficient_polynomial_value s t)<=e*`|t|^+k.+1)) in hh.
  rewrite hc add0r (real_seminorm_scale hN.1) exprS in hh.
  have heq : e*(`|t|*`|t|^+k)=`|t|*(e*`|t|^+k) by ring.
  rewrite heq in hh.
  by move:hh; rewrite (ler_pM2l (andP ht).1).
Qed.

(** Source for [finite_power_little_o_coefficients_zero]:
    the same uniqueness in the finite-power
    notation of Federer 3.1.11, p. 221.
    It applies to arbitrary normed vector coefficients,
    without a finite-dimensional target restriction. *)
Theorem finite_power_little_o_coefficients_zero (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N)
    k M (c : nat->Y) :
  (M<=k.+1)%N ->
  norm_little_o_power N (fun t=>\sum_(i<M) t^+i*:c i) k ->
  forall i, (i<M)%N -> c i= 0.
Proof.
move=>hMk ho.
pose s := [seq c i | i<-iota 0 M].
have he t : coefficient_polynomial_value s t=\sum_(i<M) t^+i*:c i.
  rewrite coefficient_polynomial_sum /s size_map size_iota.
  apply: eq_bigr=>i _.
  by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
have hs : (size s<=k.+1)%N by rewrite /s size_map size_iota.
have hsO : norm_little_o_power N (coefficient_polynomial_value s) k.
  move=>e heps; have [d [hd hb]] := ho e heps.
  exists d; split=> // t ht; rewrite he; exact: hb.
have /allP hz := vector_polynomial_little_o_coefficients_zero hN hs hsO.
move=>i hi; apply/eqP; apply: hz.
apply/mapP; exists i=> //; by rewrite mem_iota add0n leq0n hi.
Qed.
