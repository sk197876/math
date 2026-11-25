(** Federer (1969), 3.4.1, p. 310: public critical degree and its elementary range. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import CriticalValueDegreeUP CriticalValueDegreeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_value_degree_formula]: the exact scalar
    s=nu+(m-nu)/k in 3.4.1, p. 310, obtained from the public law rather
    than by unfolding the sealed implementation. *)
Lemma critical_value_degree_formula (R:realType) m nu k hk hnu:
  @CriticalValueDegree.value R m nu k hk hnu=nu%:R+(m%:R-nu%:R)/k%:R.
Proof. exact:(critical_value_degree_equation (@CriticalValueDegree.laws R m nu k hk hnu)). Qed.

(** Source for [critical_value_degree_range]: supporting the real
    degree in the Hausdorff measure of 3.4.1, p. 310. The printed
    integer range implies 0<=nu<s<=m, in particular s>0. No measure
    estimate, target dimension or finiteness hypothesis is assumed. *)
Theorem critical_value_degree_range (R:realType) m nu k hk hnu:
  nu%:R<@CriticalValueDegree.value R m nu k hk hnu<=m%:R.
Proof.
have hkR:0<(k%:R:R) by rewrite ltr0n.
have hk1:(1:R)<=k%:R by rewrite ler1n.
have hD:0<(m%:R:R)-nu%:R by rewrite subr_gt0 ltr_nat.
have hQ:0<((m%:R:R)-nu%:R)/k%:R by rewrite divr_gt0.
have hBound:((m%:R:R)-nu%:R)/k%:R<=m%:R-nu%:R.
  rewrite (ler_pdivrMr _ _ hkR);nra.
rewrite critical_value_degree_formula;apply/andP;split;lra.
Qed.

(** Source for [critical_value_degree_positive]: positive real degree
    in 3.4.1, p. 310, including the printed rank-zero case nu=0. *)
Lemma critical_value_degree_positive (R:realType) m nu k hk hnu:
  0<@CriticalValueDegree.value R m nu k hk hnu.
Proof.
have hNu:0<=(nu%:R:R) by rewrite ler0n.
exact:le_lt_trans hNu (andP (@critical_value_degree_range R m nu k hk hnu)).1.
Qed.

(** Source for [critical_value_degree_class_one]: at k=1 the
    announced dimension is the original source dimension m, as in
    the comparison with 3.2.3 in 3.4.1, p. 310. This is only the
    scalar identity; it assumes no Sard theorem. *)
Lemma critical_value_degree_class_one (R:realType) m nu hk hnu:
  @CriticalValueDegree.value R m nu 1 hk hnu=m%:R.
Proof. by rewrite critical_value_degree_formula /= divr1;ring. Qed.

(** Source for [critical_value_degree_rank_zero]: the printed
    rank-zero specialization s=m/k of 3.4.1, p. 310. *)
Lemma critical_value_degree_rank_zero (R:realType) m k hk hnu:
  @CriticalValueDegree.value R m 0 k hk hnu=m%:R/k%:R.
Proof. by rewrite critical_value_degree_formula /= subr0 add0r. Qed.
