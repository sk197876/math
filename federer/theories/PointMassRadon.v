(** Federer (1969), 4.1.11, p. 365: the point-current
    specialization of the join mass estimate uses the original
    unit point mass. Its Radon property follows directly from
    the regularity definition of 2.2.5, p. 62, and the point
    evaluation of 2.5.15, p. 108. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP PointMassMeasure PointMassRegularity RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [point_mass_radon]: on a locally compact
    Hausdorff space the original unit point mass is Radon,
    supporting the cone specialization in Federer 4.1.11,
    p. 365. Both regularity laws retain every source set. *)
Theorem point_mass_radon (R:realType) (X:topologicalType) (c:X)
    (hHausdorff:@hausdorff_space X) (hLocal:locally_compact [set:X]):
  is_radon_measure (point_mass R c).
Proof.
constructor;[exact:hHausdorff|exact:hLocal| | | | ].
- move=>K _;exact:(le_lt_trans (point_mass_le1 R c K) (ltry _)).
- move=>V _;exact:point_mass_every_set_measurable.
- move=>V _ b hBound;case:(pselect (V c))=>hV.
  + rewrite (point_mass_in R hV).
    have hK:[set c] `<=` V by move=>x ->;exact:hV.
    have h:=hBound [set c] (@compact_set1 X c) hK.
    by rewrite (@point_mass_in R X c [set c] (erefl c)) in h.
  + rewrite (point_mass_out R hV).
    have h:=hBound set0 compact0 (sub0set V).
    by rewrite point_mass_out in h.
- move=>A b hBound;case:(pselect (A c))=>hA.
  + rewrite (point_mass_in R hA).
    have h:=hBound setT openT (subsetT A).
    by rewrite (@point_mass_in R X c setT Logic.I) in h.
  + rewrite (point_mass_out R hA).
    have hClosed:closed [set c]:=@accessible_closed_set1 X (hausdorff_accessible hHausdorff) c.
    have hSub:A `<=` ~` [set c].
      move=>x hx he;apply:hA;by rewrite -he.
    have h:=hBound (~` [set c]) (closed_openC hClosed) hSub.
    rewrite point_mass_out in h;first exact:h.
    by move=>hc;exact:hc (erefl c).
Qed.
