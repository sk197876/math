(** Federer (1969), 2.10.41, printed p. 200: the diameter factor is
    sqrt(2n/(n+1)). Derive it from the summed squared-distance estimate for
    at most n+1 contact centres. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [jung_factor]: direct printed sharp
    factor sqrt(2n/(n+1)) in 2.10.41, p. 200. *)
Definition jung_factor (R : realType) (n : nat) : R := Num.sqrt (2*n%:R/(n.+1)%:R).

(** Source for [jung_factor_nonnegative]: supporting
    nonnegative square-root convention for the diameter
    bound of 2.10.41, p. 200. *)
Lemma jung_factor_nonnegative (R : realType) n : 0<=@jung_factor R n.
Proof. exact: sqrtr_ge0. Qed.

(** Source for [jung_factor_square]: supporting exact
    squared coefficient in the final calculation of
    2.10.41, p. 200, including dimension zero. *)
Lemma jung_factor_square (R : realType) n :
  (n.+1)%:R*(@jung_factor R n)^+2= 2*n%:R.
Proof.
have hn : 0<(n.+1)%:R :> R by rewrite ltr0n.
have hq : (0:R)<= 2*n%:R/(n.+1)%:R by rewrite divr_ge0 ?mulr_ge0 ?ler0n.
by rewrite /jung_factor sqr_sqrtr // mulrCA mulfV ?mulr1 // gt_eqF.
Qed.

(** Source for [jung_factor_line]: one-dimensional
    boundary of 2.10.41, p. 200: the factor
    equals one, as for the interval hull. *)
Lemma jung_factor_line (R : realType) : @jung_factor R 1= 1.
Proof. by rewrite /jung_factor mulr1 divff ?sqrtr1 // pnatr_eq0. Qed.

(** Source for [jung_contact_count_diameter_bound]: supporting
    last summation and square-root step in 2.10.41,
    p. 200. A representation with k<=n+1
    contact centres gives the same printed coefficient;
    padding to exactly n+1 terms is unnecessary. *)
Lemma jung_contact_count_diameter_bound (R : realType) n k (c d : R) :
  (0<k<=n.+1)%N -> 0<=c -> 0<=d ->
  2*k%:R*c^+2<=(k%:R-1)*d^+2 -> c+c<=@jung_factor R n*d.
Proof.
move=> /andP [hk hkn] hc hd hcount.
have hkpos : 0<k%:R :> R by rewrite ltr0n.
have hknR : k%:R<=(n.+1)%:R :> R by rewrite ler_nat.
have hdsq : 0<=d^+2 := sqr_ge0 d.
have hb : k%:R*(2*c^+2)<=k%:R*d^+2 by nra.
have hbase : 2*c^+2<=d^+2 by move: hb; rewrite (ler_pM2l hkpos).
have hgap : 0<=d^+2-2*c^+2 by rewrite subr_ge0.
have hscaled := ler_wpM2r hgap hknR.
have hdimension : 2*(n.+1)%:R*c^+2<=n%:R*d^+2.
  have hn : (n.+1)%:R=n%:R+1 :> R by rewrite -addn1 natrD.
  rewrite hn in hscaled *; nra.
have hnp : 0<(n.+1)%:R :> R by rewrite ltr0n.
have hprod := @jung_factor_square R n.
have he : (n.+1)%:R*(@jung_factor R n*d)^+2= 2*n%:R*d^+2.
  by rewrite exprMn mulrA hprod.
have hsq : (c+c)^+2<=(@jung_factor R n*d)^+2.
  rewrite -(ler_pM2l hnp) he; nra.
by move: hsq; rewrite (ler_sqr (addr_ge0 hc hc) (mulr_ge0 (@jung_factor_nonnegative R n) hd)).
Qed.
