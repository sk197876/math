(** Federer (1969), 2.5.10, p. 101: the measure restricted to the compact
    remainder Y is Radon before taking its support. The original Radon laws
    are Federer 2.2.5, pp. 62–63. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport
  MeasureFiniteClosure RadonMeasureUP RadonBorelRegularity RadonFiniteInnerRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_measure_compact_restriction]: Supporting step in
    Federer 2.5.10, p. 101, using the Radon laws of 2.2.5, pp. 62–63:
    restriction to a compact set is Radon. The compact set may be empty. *)
Theorem radon_measure_compact_restriction (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (K : set T) :
  compact K -> is_radon_measure (measure_restrict mu K).
Proof.
move=> hK; have hKm := @radon_compact_measurable R T mu hm hr K hK.
have hKclosed := compact_closed (radon_hausdorff hr) hK.
constructor.
- exact: radon_hausdorff hr.
- exact: radon_locally_compact hr.
- move=> C hC; apply: le_lt_trans _ (radon_compact_finite hr hK).
  apply: (@measure_mono R T mu hm)=> x [hx _]; exact: hx.
- move=> V hV; exact: measure_restrict_measurable (radon_open_measurable hr hV).
- move=> V hV c hc.
  apply: (@radon_finite_measurable_inner_least R T mu hm hr (K `&` V) c).
  + exact: (@measure_measurable_intersection R T mu hm K V hKm (radon_open_measurable hr hV)).
  + apply: le_lt_trans _ (radon_compact_finite hr hK).
    apply: (@measure_mono R T mu hm)=> x [hx _]; exact: hx.
  + move=> L hL hLKV.
    have hLK : L `<=` K by move=> x hx; exact: (hLKV x hx).1.
    have hLV : L `<=` V by move=> x hx; exact: (hLKV x hx).2.
    have hh := hc L hL hLV; by rewrite (measure_restrict_subset_value mu hLK) in hh.
- move=> A c hc; apply: (@radon_outer_greatest R T mu hr (K `&` A) c)=> V hV hKA.
  have ho : open (V `|` (~` K)) := openU hV (closed_openC hKclosed).
  have hAV : A `<=` V `|` (~` K).
    move=> x hx; case: (pselect (K x))=> hk; last by right.
    left; apply: hKA; by split.
  have hh := hc _ ho hAV.
  apply: le_trans hh _; apply: (@measure_mono R T mu hm)=> x [hk [hv|hn]]=> //.
Qed.
