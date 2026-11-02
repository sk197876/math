(** Federer (1969), 2.5.8, p. 100: finiteness of the operator seminorm. The
    null-norm hypothesis is Federer's erratum p. 2, book p. 100 line 3. A
    sequence of arbitrarily large unit-ball values would have a common
    L-infinity upper envelope, contradicting the finite variation bound. We
    use almost domination rather than first choosing pointwise bounded
    representatives (corrected lines 7, 9). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeSeminormUP FunctionOperatorSeminorm
  ExtendedRealBoundsUP ExtendedRealBounds DaniellIntegralUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  LinfinitySequenceEnvelope LpAlmostOrderBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linfinity_daniell_operator_finite]: the full boundedness
    argument of Federer 2.5.8, p. 100, with erratum p. 2, line 3 Boundedness
    is proved from the Daniell laws and null-norm condition. *)
Theorem linfinity_daniell_operator_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R) :
  is_daniell_integral (total_scalar_lp mu +oo) A ->
  (forall f, total_scalar_lp mu +oo f -> total_scalar_lp_norm mu +oo f=0 -> A f=0%R) ->
  function_operator_seminorm (total_scalar_lp mu +oo) A (finite_total_scalar_lp_norm mu +oo) < +oo.
Proof.
move=> hA hnull; apply: contrapT=> hbad.
have hu n : exists f : X -> R, total_scalar_lp mu +oo f /\
    (finite_total_scalar_lp_norm mu +oo f <= 1)%R /\ (n%:R < `|A f|)%R.
  apply: contrapT=> hn.
  have hbound : function_operator_seminorm (total_scalar_lp mu +oo) A
      (finite_total_scalar_lp_norm mu +oo) <= (n%:R : R)%:E.
    apply: extended_real_sup_least=> v [r [[f [hf [hN ->]]] ->]].
    rewrite lee_fin leNgt; apply/negP=> hlt; apply: hn; exists f; by split=> //; split.
  apply: hbad; exact: le_lt_trans hbound (ltry _).
pose f n := projT1 (cid (hu n)).
have hf n := projT2 (cid (hu n)).
have hnorm n : total_scalar_lp_norm mu +oo (f n) <= 1.
  rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm +oo (f n) (hf n).1) lee_fin.
  exact: (hf n).2.1.
have [g [hg [hg0 [hgn hupper]]]] := @linfinity_sequence_has_upper_envelope R X mu hm f
  (fun n => (hf n).1) hnorm.
have [b hb] := @lp_daniell_almost_order_bound R X mu hm +oo A (leey _) hA hnull g hg hg0.
pose n := Num.bound `|b|.
have hbn : (b < n%:R)%R := le_lt_trans (ler_norm b) (archi_boundP (normr_ge0 b)).
have hlt := lt_trans hbn (hf n).2.2.
have hle := hb (f n) (hf n).1 (hupper n).
by have := lt_le_trans hlt hle; rewrite ltxx.
Qed.
