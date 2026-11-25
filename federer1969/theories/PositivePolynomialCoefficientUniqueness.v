(** Federer (1969), 3.2.36, p. 273: comparison of the
    positive-radius tube polynomials uses the internal root-count theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_coefficient_polynomial_zero]: the polynomial
    coefficient comparison in Federer 3.2.36, p. 273. Vanishing
    at every positive radius supplies enough distinct positive natural
    scalars for the project's synthetic-division root-count theorem
    from 1.10.4, p. 46. No external polynomial library or
    equality at negative radii is assumed. *)
Lemma positive_coefficient_polynomial_zero (R:realType) (W:lmodType R) (s:seq W):
  (forall t:R,0<t ->coefficient_polynomial_value s t=0) ->all (pred1 0) s.
Proof.
move=>hz.
pose r:=[seq (i%:R:R)|i<-iota 1 (size s)].
apply:(@coefficient_polynomial_roots R W (size s) s r)=>//.
- by rewrite /r size_map size_iota.
- by rewrite /r (map_inj_uniq (characteristic_zero_nat_injective (@pchar_num R))) iota_uniq.
- move=>x /mapP[i hi ->]; apply:hz; rewrite ltr0n.
  by move:hi; rewrite mem_iota=>/andP[hi _].
Qed.

(** Source for [positive_finite_power_coefficients_unique]: equality
    of coefficients of the two positive-radius polynomials in Federer
    3.2.36, p. 273. It follows by subtracting finite coefficient
    lists and applying the already proved internal root count. *)
Theorem positive_finite_power_coefficients_unique (R:realType) (W:lmodType R)
    N (c d:nat->W):
  (forall t:R,0<t ->\sum_(i<N) t^+i*:c i=\sum_(i<N) t^+i*:d i) ->
  forall i,(i<N)%N ->c i=d i.
Proof.
move=>hEqual.
pose s:=[seq c i-d i|i<-iota 0 N].
have hZero t:0<t ->coefficient_polynomial_value s t=0.
  move=>ht; rewrite coefficient_polynomial_sum /s size_map size_iota.
  have hValue: \sum_(i<N) t^+i*:nth 0 [seq c j-d j|j<-iota 0 N] i=
      \sum_(i<N) t^+i*:(c i-d i).
    apply:eq_bigr=>i _.
    by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
  rewrite hValue; under eq_bigr do rewrite scalerBr.
  by rewrite sumrB hEqual // subrr.
have /allP hAll:=positive_coefficient_polynomial_zero hZero.
move=>i hi; apply/eqP; rewrite -subr_eq0; apply:hAll.
apply/mapP; exists i=>//; by rewrite mem_iota add0n leq0n hi.
Qed.
