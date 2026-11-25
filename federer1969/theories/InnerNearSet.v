(** Federer (1969), 1.7.13, p. 37: the nonempty closed approximating sets
    C_s. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import classical_sets topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NearSet.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable a : M.
Variable C : set M.
Variable d : R.
Hypothesis hd : is_inner_set_distance hB a C d.

(** Source for [inner_near_set]: Federer 1.7.13, p. 37,
    the displayed set C_s: points of C whose squared distance
    to a is at most d squared plus s squared. Symmetry permits
    writing a-x in place of the printed x-a. *)
Definition inner_near_set (s : R) : set M :=
  [set x | C x /\ inner_norm hB (a-x)^+2 <= d^+2+s^+2].

(** Source for [inner_near_set_ball]: Federer 1.7.13, p. 37, supporting
    closed-ball description of C_s *)
Lemma inner_near_set_ball s : inner_near_set s =
  C `&` closed_ball_ normr a (Num.sqrt (d^+2+s^+2)).
Proof.
have hq : 0 <= d^+2+s^+2 by exact: addr_ge0 (sqr_ge0 _) (sqr_ge0 _).
apply/seteqP; split=> x [hx hn]; split=> //.
- change (inner_norm hB (a-x) <= Num.sqrt (d^+2+s^+2)).
  by rewrite -(ler_sqr (inner_norm_nonnegative hB _) (sqrtr_ge0 _)) sqr_sqrtr.
- change (is_true (inner_norm hB (a-x) <= Num.sqrt (d^+2+s^+2))) in hn.
  by move: hn; rewrite -(ler_sqr (inner_norm_nonnegative hB _) (sqrtr_ge0 _)) sqr_sqrtr.
Qed.

(** Source for [inner_near_set_closed]: Federer 1.7.13,
    p. 37, C_s is closed. Only the general topological fact
    that a closed ball is closed is used here. *)
Lemma inner_near_set_closed s : closed C -> closed (inner_near_set s).
Proof.
move=> hC; rewrite inner_near_set_ball; apply: closedI; first exact hC.
exact: closed_closed_ball_.
Qed.

(** Source for [inner_near_set_nested]: Federer 1.7.13,
    p. 37, C_r is contained in C_s when 0<r<=s. *)
Lemma inner_near_set_nested r s : 0 < r -> r <= s ->
    inner_near_set r `<=` inner_near_set s.
Proof.
move=> hr hrs x [hx hn]; split=> //; apply: le_trans hn _.
rewrite lerD2l; exact: lerXn2r (ltW hr) (le_trans (ltW hr) hrs) hrs.
Qed.

(** Source for [inner_near_set_nonempty]: Federer 1.7.13,
    p. 37, C_s is nonempty for every s>0, by the approximation
    property of the infimum d. *)
Lemma inner_near_set_nonempty s : 0 < s -> inner_near_set s !=set0.
Proof.
move=> hs.
have hd0 := inner_set_distance_nonnegative_law hd.
have hq0 : 0 <= d^+2+s^+2 by exact: addr_ge0 (sqr_ge0 _) (sqr_ge0 _).
have hlt : d < Num.sqrt (d^+2+s^+2).
  rewrite -(ltr_sqr hd0 (sqrtr_ge0 _)) sqr_sqrtr // ltrDl.
  rewrite expr2; exact: mulr_gt0.
have he : 0 < Num.sqrt (d^+2+s^+2)-d by rewrite subr_gt0.
have [x [hx hn]] := inner_set_distance_approx_law hd he.
rewrite [d+(_-d)]addrC subrK in hn.
exists x; split=> //.
have hh := ltW hn.
by move: hh; rewrite -(ler_sqr (inner_norm_nonnegative hB _) (sqrtr_ge0 _)) sqr_sqrtr.
Qed.
End NearSet.
Arguments inner_near_set {R V B} hB a C d s.
