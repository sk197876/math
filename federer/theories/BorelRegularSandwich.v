(** Federer (1969), 2.2.3, p. 61, Borel inner and outer sets differing by a
    null set. Here the statement retains Federer's finite hypothesis. Source
    editions: BorelRegularMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_finite_sandwich]: Federer 2.2.3, p. 61,
    displayed assertion and following construction: for measurable A of
    finite measure, Borel D and B satisfy D subset A subset B and mu(B minus
    D)=0. Choose B of equal measure, then a null Borel cover E of B minus A,
    and D=B minus E. *)
Theorem borel_regular_finite_sandwich (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) A :
  measure_measurable mu A -> mu A < +oo ->
  exists D B, borel_set D /\ borel_set B /\
    D `<=` A /\ A `<=` B /\ mu (B `\` D) = 0.
Proof.
move=> hA hf; have [B [hAB [hB he]]] := borel_regular_cover hr A.
have hfin : mu A \is a fin_num.
  by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R _ mu hm A).
have hBA : mu (B `\` A) = 0.
  have hi : B `&` A = A.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hAB.
  have h := hA B; rewrite hi -he in h.
  have hc := congr1 (fun t => t - mu A) h.
  by rewrite subee // (addeC (mu A) (mu (B `\` A))) addeK // in hc.
have [E [hBE [hE heE]]] := borel_regular_cover hr (B `\` A).
have hE0 : mu E = 0 by rewrite -heE hBA.
exists (B `\` E), B; split; first exact: borel_set_difference hB hE.
split=> //; split.
- move=> x [hb hn]; case: (pselect (A x))=> ha //.
  exfalso; apply: hn; apply: hBE; by split.
- split=> //; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  rewrite -hE0; apply: (@measure_mono R _ mu hm _ E).
  move=> x [hb hn]; case: (pselect (E x))=> he' //.
  exfalso; apply: hn; by split.
Qed.
