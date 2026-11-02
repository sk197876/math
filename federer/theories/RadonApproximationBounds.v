(** Federer (1969), 2.2.5, p. 63, choices of open V and compact C with small
    complementary measure. Source context: RadonMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RadonMeasureUP RadonMeasureBounds
  RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_finite_open_error]: Federer 2.2.5, p. 63, first choice
    of V: a finite-measure measurable set A has an open superset of finite
    measure with arbitrarily small excess. *)
Lemma radon_finite_open_error (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) A epsilon :
  measure_measurable mu A -> mu A < +oo -> (0 < epsilon)%R ->
  exists V, open V /\ A `<=` V /\ mu V < +oo /\ mu (V `\` A) < epsilon%:E.
Proof.
move=> hA hf he; have hfin : mu A \is a fin_num.
  by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R _ mu hm A).
have hlt : mu A < mu A + epsilon%:E.
  by rewrite -{1}[mu A]adde0 lteD2lE // lte_fin.
have [V [ho [hAV hv]]] := radon_outer_strict_approximation hr hlt.
exists V; split=> //; split=> //; split.
- apply: lt_trans hv _; apply: lte_add_pinfty=> //; exact: ltry.
- have hi : V `&` A = A.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hAV.
  by rewrite (hA V) hi lteD2lE // in hv.
Qed.

(** Source for [radon_finite_compact_error]: Federer 2.2.5, p. 63, choice of
    compact C inside finite-measure open V with mu(V minus C) below a
    prescribed positive tolerance. *)
Lemma radon_finite_compact_error (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) V epsilon :
  open V -> mu V < +oo -> (0 < epsilon)%R ->
  exists C, compact C /\ C `<=` V /\ mu (V `\` C) < epsilon%:E.
Proof.
move=> ho hf he; have hfin : mu V \is a fin_num.
  by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R _ mu hm V).
have hlt : mu V - epsilon%:E < mu V.
  rewrite lte_subel_addr // -{1}[mu V]adde0 lteD2lE // lte_fin; exact he.
have [C [hc [hCV hlarge]]] := radon_inner_strict_approximation hr ho hlt.
have hC := radon_compact_measurable hm hr hc.
have hi : V `&` C = C.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hCV.
have hCf : mu C \is a fin_num.
  rewrite ge0_fin_numE; first exact: (@radon_compact_finite R T mu hr C hc).
  exact: (@measure_nonnegative R _ mu hm C).
exists C; split=> //; split=> //.
by rewrite lte_subel_addr // (hC V) hi lteD2lE // in hlarge.
Qed.
