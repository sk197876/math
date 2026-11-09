(** Federer (1969), 3.3.4, p. 288: a full plane
    satisfies either the actual source-accumulation alternative
    or the original ordinary zero-growth alternative. This
    proves the endpoint pointwise, without a measure on planes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric StructurePlaneGrowth StructureSourceIsolation
  StructureIsolatedCentre MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_full_plane_trichotomy]: the m=0
    endpoint of Federer 3.3.4, p. 288, including
    the zero-dimensional ambient space. Accumulation is tested
    on the original punctured source; otherwise an actual
    positive source-free neighbourhood makes every cone mass zero.
    The supporting conclusion also holds for every growth degree. *)
Theorem structure_full_plane_trichotomy (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a
    (V:G (R_n R n) n):
  is_measure phi ->structure_plane_trichotomy m phi A a V.
Proof.
move=>hMeasure.
case:(pselect (structure_plane_accumulation A a V))=>hAccum.
  by right; right.
have hNo:~closure [set x:inner_metric_space (@euclidean_inner_productP R n)|A x /\ x!=a] a.
  move=>h; apply:hAccum; exact:(structure_full_plane_accumulation A a V).2 h.
have [d [hd hEmpty]]:=structure_no_source_accumulation_isolated hNo.
left; exact:(@structure_isolated_centre_zero_growth R n n m phi A a V d
  hMeasure hd hEmpty).
Qed.
