(** Federer (1969), 2.10.22, pp. 184–185: supporting selection of a largest
    positive cost from a finite-cost cover. The formal proof orders costs
    and later recovers shrinking diameters from compactness and positivity.
    This avoids assuming that zero-diameter members of an infinite cover
    admit the printed decreasing-diameter enumeration. The theorem's
    hypotheses and conclusion are unchanged. Summation background:
    2.1.1(12), p. 53 *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal lra.
From Federer Require Import NonnegativeSum NonnegativeSumCountable FiniteRealMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_positive_cost_maximum]: supporting
    largest-cost selection for the cover extraction
    in 2.10.22, pp. 184–185. Finite summation
    makes every positive cost superlevel finite, so
    a positive value gives an attained maximum. *)
Theorem summable_positive_cost_maximum (R : realType) (I : choiceType)
    (G : set I) (w : I -> R) (M : R) :
  (forall x, G x -> 0<=w x) ->
  (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E ->
  (G `&` [set x | 0<w x]) !=set0 ->
  exists a, G a /\ 0<w a /\ forall x, G x -> w x<=w a.
Proof.
move=> hw hsum [b [hb hwb]].
change (is_true (0<w b)) in hwb.
pose c := w b/2.
have hc : 0<c by rewrite /c divr_gt0 // ltr0n.
have hfin : (nonnegative_sum G (fun x=>(w x)%:E)< +oo)%E := le_lt_trans hsum (ltry M).
have hfinite := @nonnegative_sum_threshold_finite R I G (fun x=>(w x)%:E) c hc hfin.
pose A := G `&` [set x | c%:E<=(w x)%:E]%E.
have hA : finite_set A := hfinite.
have hbA : A b.
  split; first exact hb.
  change (is_true (c<=w b)); rewrite /c; lra.
have hne : A !=set0 by exists b.
have [a [[ha hca] hmax]] := finite_nonempty_real_maximum w hA hne.
have hwa : 0<w a.
  have hh : c<=w a := hca.
  exact: lt_le_trans hc hh.
exists a; split=> //; split=> // x hx.
case: (leP c (w x))=> hcx.
- apply: hmax; split; [exact hx|exact hcx].
- have hh := hmax b hbA; rewrite /c in hcx; lra.
Qed.
