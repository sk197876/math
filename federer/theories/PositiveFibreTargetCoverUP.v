(** Federer (1969), 3.2.32, pp. 269–270: independent
    target-cover laws for passing from the finite fibre
    thresholds of 3.2.31 to the positive fibre locus. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RectifiableSetUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_fibre_target_cover]: supporting the
    reciprocal-threshold passage in the proof of Federer 3.2.32,
    p. 270. Disjoint finite rectifiable Borel pieces contain
    the entire positive fibre locus and add only a null target
    remainder. The independent laws allow source preimages to
    be proved measurable without assuming that completed target
    measurable sets always have measurable preimages. *)
Record is_positive_fibre_target_cover (R:realType) (X:metricType R)
    (beta:set X->\bar R) mu (Y:set X) (D:nat->set X):Prop:={
  (** Source for [positive_fibre_cover_borel]: supporting Borel target
      pieces in the application of 3.2.22 for 3.2.32, p. 270. *)
  positive_fibre_cover_borel:forall j,borel_set (D j);
  (** Source for [positive_fibre_cover_rectifiable]: finite rectifiable
      target pieces supplied by 3.2.31 in 3.2.32, p. 270. *)
  positive_fibre_cover_rectifiable:forall j,is_measure_m_rectifiable beta mu (D j);
  (** Source for [positive_fibre_cover_disjoint]: supporting disjoint
      target summation in the limiting argument of 3.2.32, p. 270. *)
  positive_fibre_cover_disjoint:forall i j,i!=j ->forall x,D i x ->D j x ->False;
  (** Source for [positive_fibre_cover_contains]: all positive fibre
      values exceed some reciprocal threshold in 3.2.32, p. 270. *)
  positive_fibre_cover_contains:Y `<=` \bigcup_j D j;
  (** Source for [positive_fibre_cover_null_excess]: supporting null
      target error from Borel hulls in 3.2.32, pp. 269–270. *)
  positive_fibre_cover_null_excess:beta ((\bigcup_j D j) `\` Y)=0
}.
