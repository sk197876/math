(** Federer (1969), 3.3.2, pp. 287–288: openness of the
    parameter sets on which a compact subset remains in the cone,
    and continuity from below for the outer measure. This general
    supporting lemma keeps only the standing closed-set measurability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import CompactProductTube TopologicalProductMaps
  LipschitzFunctionCompact StructureOpenCompactInner MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_open_fibre_mass_neighbourhood]: the
    compact-subset neighbourhood argument in Federer 3.3.2,
    pp. 287–288, for an arbitrary open incidence set. Every
    finite strict mass threshold persists in an open parameter
    neighbourhood, including at infinite-mass fibres. *)
Theorem structure_open_fibre_mass_neighbourhood (R:realType)
    (P:topologicalType) (X:metricType R) (mu:set X->\bar R)
    (a:X) (U:set (P*X)) (p:P) (b:R):
  is_measure mu ->metric_boundedly_compact X ->
  (forall C,closed C->measure_measurable mu C) ->
  open U ->b%:E<mu [set x|U (p,x)] ->
  exists V,open V /\ V p /\
    forall q,V q->b%:E<mu [set x|U (q,x)].
Proof.
move=>hm hX hClosed hU hLower.
have hF:continuous (fun x:X=>(p,x):P*X).
  apply:topological_pair_continuous; first exact:cst_continuous.
  by move=>x; exact:cvg_id.
have hFibre:open [set x:X|U (p,x)].
  exact:(open_comp (fun x _=>hF x) hU).
have [K [hK [hKU hMass]]]:=structure_open_compact_inner_strict
  a hm hX hClosed hFibre hLower.
have [V [W [hV [hp [_ [hKW hTube]]]]]]:=compact_product_open_tube hK hU hKU.
exists V; split=>//; split=>// q hq.
apply:lt_le_trans hMass _; apply:(measure_mono hm)=>x hx.
exact:(hTube (q,x) (conj hq (hKW x hx))).
Qed.

(** Source for [structure_open_fibre_mass_superlevel]: the
    open strict mass superlevel in the proof of Federer 3.3.2,
    pp. 287–288, before the positive continuous normalizing
    factors and the corrected countable limsup formula are applied. *)
Theorem structure_open_fibre_mass_superlevel (R:realType)
    (P:topologicalType) (X:metricType R) (mu:set X->\bar R)
    (a:X) (U:set (P*X)) (b:R):
  is_measure mu ->metric_boundedly_compact X ->
  (forall C,closed C->measure_measurable mu C) ->
  open U ->open [set p:P|b%:E<mu [set x|U (p,x)]].
Proof.
move=>hm hX hClosed hU; rewrite openE=>p hp.
have [V [hV [hpV hLower]]]:=structure_open_fibre_mass_neighbourhood
  a hm hX hClosed hU hp.
have hn:nbhs p V by rewrite openE in hV; exact:(hV p hpV).
apply:(@filterS _ (nbhs p) _ V _ _ hn)=>q hq; exact:(hLower q hq).
Qed.
