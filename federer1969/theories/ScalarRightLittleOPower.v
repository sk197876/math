(** Federer (1969), 3.4.5, p. 321: one-sided
    Taylor comparison supporting the flat-coefficient argument
    for the example cited to Cartan (1957), pp. 97–99.
    The underlying Taylor remainder is 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_right_little_o_power]: the original
    positive-side power decay used to compare actual Taylor
    coefficients at the flat endpoint, supporting the example
    cited in 3.4.5, p. 321. The domain excludes zero. *)
Definition scalar_right_little_o_power (R:realType) (f:R->R) (m:nat):Prop:=
  forall epsilon:R,0<epsilon ->exists r:R,0<r /\
    forall t:R,0<t<r ->`|f t|<=epsilon*t^+m.

(** Source for [scalar_little_o_right_restriction]: a true
    two-sided Taylor remainder retains its estimate on positive
    increments, supporting 3.4.5, p. 321. *)
Lemma scalar_little_o_right_restriction (R:realType) (f:R->R) m:
  norm_little_o_power (fun t:R^o=>`|t|) f m ->scalar_right_little_o_power f m.
Proof.
move=>h epsilon hEpsilon;have [r [hr hBound]]:=h epsilon hEpsilon.
exists r;split;first exact:hr.
move=>t ht;have hNorm:`|t|=t:=ger0_norm (ltW (andP ht).1).
have ht':0<`|t|<r by rewrite hNorm.
by have hh:=hBound t ht';rewrite hNorm in hh.
Qed.

(** Source for [scalar_right_monomial_coefficient_zero]: if
    an actual function and its remainder after one monomial
    both vanish faster than that positive power, the monomial
    coefficient is zero. This proves the finite-order bridge
    needed in the example cited at 3.4.5, p. 321. *)
Theorem scalar_right_monomial_coefficient_zero (R:realType) (f:R->R) m (c:R):
  scalar_right_little_o_power f m ->
  scalar_right_little_o_power (fun t=>f t-t^+m*c) m ->c=0.
Proof.
move=>hFunction hRemainder.
apply/eqP;rewrite -normr_eq0;apply/eqP.
apply/eqP;rewrite eq_le;apply/andP;split;last exact:normr_ge0.
rewrite leNgt;apply/negP=>hC.
pose epsilon:R:=`|c|/4.
have hEpsilon:0<epsilon by rewrite /epsilon divr_gt0 // ltr0n.
have [r [hr hF]]:=hFunction epsilon hEpsilon.
have [s [hs hRem]]:=hRemainder epsilon hEpsilon.
pose t:R:=Num.min r s/2.
have hMin:0<Num.min r s by rewrite lt_min hr hs.
have ht:0<t by rewrite /t divr_gt0 // ltr0n.
have htMin:t<Num.min r s by rewrite /t;lra.
have hMinR:Num.min r s<=r by rewrite ge_min lexx.
have htr:t<r:=lt_le_trans htMin hMinR.
have hMinS:Num.min r s<=s by rewrite ge_min lexx orbT.
have hts:t<s:=lt_le_trans htMin hMinS.
have hFt:=hF t (introT andP (conj ht htr)).
have hRt:=hRem t (introT andP (conj ht hts)).
have hTriangle:=ler_normB (f t) (f t-t^+m*c).
have hIdentity:f t-(f t-t^+m*c)=t^+m*c by ring.
rewrite hIdentity normrM in hTriangle.
have hPower:0<t^+m:=exprn_gt0 m ht.
rewrite (ger0_norm (ltW hPower)) in hTriangle.
rewrite /epsilon in hFt hRt.
nra.
Qed.
