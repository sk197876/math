(** Federer (1969), 2.2.3, pp. 61–62: Borel
    regularity on a relative subspace. Supporting the actual
    orthogonal-group Hausdorff measure in 3.2.48, p. 284;
    the subspace carries its original relative topology. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology subtype_topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages IsotropyGroupTopology OpenSubspaceMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subspace_image_measure_laws]: restriction to
    a relative carrier is a measure, by 2.1.2, p. 54;
    supporting Hausdorff measure on the actual compact group
    in 3.2.48, p. 284. No openness is needed. *)
Lemma subspace_image_measure_laws (R:realType) (X:topologicalType)
    (S:set X) (mu:set X->\bar R):
  is_measure mu ->is_measure (open_subspace_measure (S:=S) mu).
Proof.
move=>hm; constructor.
- move=>A; exact (measure_nonnegative hm _).
- move=>A F hF hCover.
  apply:(measure_indexed_cover hm hF _).
  move=>x [a ha <-]; have [B hB haB]:=hCover a ha.
  exists B; first exact hB; by exists a.
Qed.

(** Source for [subspace_borel_regular_measure]: the Borel
    hull law of 2.2.3, p. 61, on the relative
    carrier. Intersect an ambient Borel hull with the
    carrier and use both monotonicity inequalities; no measurable
    or null carrier excess is assumed. Supporting 3.2.48, p. 284. *)
Theorem subspace_borel_regular_measure (R:realType) (X:topologicalType)
    (S:set X) (mu:set X->\bar R):
  is_measure mu ->is_borel_regular_measure mu ->
  is_borel_regular_measure (open_subspace_measure (S:=S) mu).
Proof.
move=>hm hReg.
pose Y:=set_type S.
constructor.
- move=>U [V hV <-] A.
  rewrite /open_subspace_measure.
  have hVMeas:=borel_regular_open_measurable hReg hV.
  rewrite (hVMeas (set_val @` A)).
  have hIntersection:set_val @` (A `&` set_val @^-1` V)=(set_val @` A) `&` V.
    apply/seteqP; split=>x.
    + move=>[a [ha hVa] <-]; split; first by exists a.
      exact hVa.
    + move=>[[a ha <-] hVa]; exists a; by split.
  have hDifference:set_val @` (A `\` set_val @^-1` V)=(set_val @` A) `\` V.
    apply/seteqP; split=>x.
    + move=>[a [ha hNot] <-]; split; first by exists a.
      exact hNot.
    + move=>[[a ha <-] hNot]; exists a; by split.
  by rewrite hIntersection hDifference.
- move=>A; have [B [hCover [hB hMass]]]:=borel_regular_cover hReg (set_val @` A).
  exists (set_val @^-1` B:set Y); split.
  + move=>a ha; exact (hCover _ (ex_intro2 _ _ a ha erefl)).
  + split.
    * exact (@continuous_borel_preimage Y X set_val (@set_type_val_continuous X S) B hB).
    * rewrite /open_subspace_measure.
      apply/eqP; rewrite eq_le; apply/andP; split.
      -- apply:(@measure_mono R X mu hm _ _)=>x [a ha <-]; exists a; last reflexivity.
         exact (hCover _ (ex_intro2 _ _ a ha erefl)).
      -- rewrite hMass; apply:(@measure_mono R X mu hm _ _)=>x [a ha <-]; exact ha.
Qed.
