(** Corrected zero-denominator convention for Federer (1969),
    2.10.17(2)–(3), p. 179. Extend only these nonnegative zero- denominator
    cases; preserve the existing partial arithmetic elsewhere, including
    infinity/infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealConventions PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_divide]: corrected density quotient for
    2.10.17, p. 179. Negative numbers divided by zero and pairs of
    infinities remain outside its domain. *)
Definition caratheodory_density_divide (R : realType) (x y : \bar R) :=
  if y==0 then
    if x==0 then Some 0 else if 0<x then Some +oo else None
  else extended_divide x y.

(** Source for [caratheodory_density_divide_zero_zero]: supporting explicit
    0/0=0 convention for the corrected 2.10.17, p. 179 The original
    arithmetic is unchanged. *)
Lemma caratheodory_density_divide_zero_zero (R : realType) :
  caratheodory_density_divide (0 : \bar R) 0=Some 0.
Proof. by rewrite /caratheodory_density_divide eqxx. Qed.

(** Source for [caratheodory_density_divide_positive_zero]: supporting
    a/0=infinity for a>0 in the corrected 2.10.17, p. 179 *)
Lemma caratheodory_density_divide_positive_zero (R : realType) (x : \bar R) :
  0<x -> caratheodory_density_divide x 0=Some +oo.
Proof. by move=> hx; rewrite /caratheodory_density_divide eqxx (gt_eqF hx) hx. Qed.

(** Source for [caratheodory_density_divide_nonzero]: supporting agreement
    with the original quotient on nonzero denominators for 2.10.17, p. 179. *)
Lemma caratheodory_density_divide_nonzero (R : realType) (x y : \bar R) :
  y!=0 -> caratheodory_density_divide x y=extended_divide x y.
Proof. by move=> hy; rewrite /caratheodory_density_divide (negPf hy). Qed.

(** Source for [caratheodory_density_divide_infinities]: supporting retained
    partial domain for 2.10.17, p. 179. *)
Lemma caratheodory_density_divide_infinities (R : realType) :
  caratheodory_density_divide (+oo : \bar R) +oo=None.
Proof. by []. Qed.

(** Source for [caratheodory_density_divide_finite_denominator]: supporting
    domain fact for the corrected 2.10.17, p. 179. Every nonnegative
    numerator has a defined density quotient at a finite nonnegative cost,
    including cost zero. *)
Lemma caratheodory_density_divide_finite_denominator (R : realType) (x y : \bar R) :
  0<=x -> 0<=y -> y < +oo -> exists z, caratheodory_density_divide x y=Some z.
Proof.
move=> hx hy hyf.
case: (eqVneq y 0)=> [->|hy0].
- case: (eqVneq x 0)=> [->|hx0].
  + exists 0; exact: caratheodory_density_divide_zero_zero.
  + exists +oo; apply: caratheodory_density_divide_positive_zero.
    by rewrite lt_def hx0 hx.
- rewrite (caratheodory_density_divide_nonzero x hy0) /extended_divide hy0.
  have hfin : y \is a fin_num by rewrite ge0_fin_numE.
  rewrite hfin orbT; by exists (x/y).
Qed.

(** Source for [caratheodory_density_finite_cost_bound]: supporting
    inequality transfer for the corrected 2.10.17(2), p. 179. *)
Lemma caratheodory_density_finite_cost_bound (R : realType) (x y : \bar R) (t : R) z :
  0<=x -> 0<=y -> y < +oo ->
  caratheodory_density_divide x y=Some z -> z<=t%:E -> x<=t%:E*y.
Proof.
move=> hx hy hyf.
case: (eqVneq y 0)=> [->|hy0].
- case: (eqVneq x 0)=> [->|hx0].
  + rewrite caratheodory_density_divide_zero_zero=> -[<-] _; by rewrite mule0.
  + have hxp : 0<x by rewrite lt_def hx0 hx.
    rewrite (caratheodory_density_divide_positive_zero hxp)=> -[<-].
    by rewrite leNgt ltry.
- have hfin : y \is a fin_num by rewrite ge0_fin_numE.
  rewrite (caratheodory_density_divide_nonzero x hy0) /extended_divide hy0 hfin orbT=> -[<-] hz.
  have hbp : 0<y by rewrite lt_def hy0 hy.
  have hc : (x/y)*y=x.
    clear hy hy0 hfin hz.
    move: hbp hyf; case: y=> [b| |] hb hf //.
    have hbR : (0<b)%R by move: hb; rewrite lte_fin.
    by rewrite inver (gt_eqF hbR) -muleA -EFinM mulVf ?gt_eqF // mule1.
  have hh := lee_wpmul2r hy hz.
  by rewrite hc in hh.
Qed.
