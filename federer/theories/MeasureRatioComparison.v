(** The cellwise ratio comparison in Federer (1969), 2.9.3, p. 154. On
    bounded auxiliary cells, the original class M makes both measures
    finite; the quotient graph excludes zero denominators. Multiplication by
    a positive finite denominator then yields the printed mass inequality.
    Source context and the strict threshold difference:
    CoveringLowerSublevel.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureDerivates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_ratio_comparison]: supporting
    arithmetic for alpha(S)<=c beta(S) in Federer 2.9.3,
    p. 154. This strict supporting bound assumes
    exactly the finite numerator and positive finite denominator
    supplied by the bounded auxiliary cells, and uses only the
    quotient graph and its public evaluation law. *)
Lemma finite_measure_ratio_comparison (R : realType) (X : Type)
    (alpha beta : set X -> \bar R) S (c : R) y :
  alpha S \is a fin_num -> beta S \is a fin_num -> 0<beta S ->
  partial_function_graph (measure_ratio_function alpha beta) S y -> y<c%:E ->
  alpha S<c%:E * beta S.
Proof.
move=> ha hb hbp hy hlt.
pose a := fine (alpha S); pose b := fine (beta S).
have hea : alpha S=a%:E by rewrite /a fineK.
have heb : beta S=b%:E by rewrite /b fineK.
have hbr : (0<b)%R by move: hbp; rewrite heb lte_fin.
have heval := @measure_ratio_positive_finite_denominator R X alpha beta S hbp hb.
have hey := @partial_function_single_valued (set X) (\bar R)
  (measure_ratio_function alpha beta) S y (alpha S/beta S) hy heval.
move: hlt; rewrite hey hea heb inver (gt_eqF hbr) -EFinM lte_fin ltr_pdivrMr // => hlt.
Qed.
