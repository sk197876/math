(** Reciprocal arithmetic supporting Federer (1969), 2.9.4, p. 154, final
    proof display. On bounded cells, M gives finite measures. A positive
    quotient threshold then forces both masses positive and permits
    reversing the ordinary partial quotient. The strict statement below
    supports Federer's original strict bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureDerivates PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_ratio_reversal]: supporting
    finite-cell version of the reciprocal implication in
    Federer 2.9.4, p. 154. The quotient graph
    excludes denominator zero; the strict positive threshold
    also excludes a zero numerator before inversion. *)
Lemma finite_measure_ratio_reversal (R : realType) (X : Type)
    (alpha beta : set X -> \bar R) S (d : R) y :
  alpha S \is a fin_num -> beta S \is a fin_num -> 0<=beta S -> (0<d)%R ->
  partial_function_graph (measure_ratio_function alpha beta) S y -> d%:E<y ->
  exists z, partial_function_graph (measure_ratio_function beta alpha) S z /\ z<(d^-1)%:E.
Proof.
move=> haf hbf hbn hd hy hlt.
have hbne : beta S!=0.
  apply/eqP=> hz; apply: (@measure_ratio_zero_denominator R X alpha beta S hz); by exists y.
have hbp : 0<beta S by rewrite lt_def hbne hbn.
pose a := fine (alpha S); pose b := fine (beta S).
have hea : alpha S=a%:E by rewrite /a fineK.
have heb : beta S=b%:E by rewrite /b fineK.
have hbr : (0<b)%R by move: hbp; rewrite heb lte_fin.
have heval := @measure_ratio_positive_finite_denominator R X alpha beta S hbp hbf.
have hey := @partial_function_single_valued (set X) (\bar R)
  (measure_ratio_function alpha beta) S y (alpha S/beta S) hy heval.
have hda : (d*b<a)%R.
  by move: hlt; rewrite hey hea heb inver (gt_eqF hbr) -EFinM lte_fin ltr_pdivlMr.
have hap : (0<a)%R := lt_trans (mulr_gt0 hd hbr) hda.
have hape : 0<alpha S by rewrite hea lte_fin.
exists (beta S/alpha S); split.
- exact: measure_ratio_positive_finite_denominator hape haf.
- rewrite hea heb inver (gt_eqF hap) -EFinM lte_fin ltr_pdivrMr //.
  rewrite (mulrC (d^-1)%R a) ltr_pdivlMr //.
  by rewrite mulrC.
Qed.
