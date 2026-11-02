(** Federer (1969), 2.2.5, p. 63, compact inner approximation of
    finite-measure measurable sets. Source context: RadonMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit RadonMeasureUP
  RadonMeasureBounds RadonApproximationBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_compact_approximation]: Federer 2.2.5, p. 63,
    approximation theorem: if A is measurable with finite measure and
    epsilon is positive, it contains a compact K with mu(A minus K) less
    than epsilon. The proof follows the book's open V and W and compact C
    construction. *)
Theorem radon_compact_approximation (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) A epsilon :
  measure_measurable mu A -> mu A < +oo -> (0 < epsilon)%R ->
  exists K, compact K /\ K `<=` A /\ mu (A `\` K) < epsilon%:E.
Proof.
move=> hA hf he; have hh : (0 < epsilon / 2)%R by rewrite divr_gt0 // ltr0n.
have [V [hV [hAV [hVf hv]]]] := radon_finite_open_error hm hr hA hf hh.
have [W [hW [hVW hw]]] := radon_outer_strict_approximation hr hv.
have [C [hC [hCV hc]]] := radon_finite_compact_error hm hr hV hVf hh.
exists (C `\` W); split.
- rewrite setDE; exact: compact_closedI hC (open_closedC hW).
- split.
  + move=> x [hx hn]; case: (pselect (A x))=> ha //.
    exfalso; apply: hn; apply: hVW; split=> //; exact: hCV.
  + have hcover : A `\` (C `\` W) `<=` (V `\` C) `|` W.
      move=> x [ha hn]; case: (pselect (W x))=> hw'; first by right.
      left; split; first exact: hAV.
      move=> hc'; apply: hn; by split.
    apply: le_lt_trans (@measure_binary_cover R _ mu hm _ _ _ hcover) _.
    have hWfin : mu W \is a fin_num.
      rewrite ge0_fin_numE; last exact: (@measure_nonnegative R _ mu hm W).
      exact: lt_trans hw (ltry _).
    have hs := lte_leD hWfin hc (ltW hw).
    have heq : (epsilon / 2 + epsilon / 2)%R = epsilon.
      exact: esym (splitr epsilon).
    by rewrite -EFinD heq in hs.
Qed.
