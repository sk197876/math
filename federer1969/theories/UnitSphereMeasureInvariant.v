(** Federer (1969), 3.2.13, p. 251: Hausdorff measure
    over the unit sphere is invariant under its orthogonal action.
    The assertion holds for every subset, not only measurable sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal
  topology subtype_topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric Hom
  OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  UnitSphereSpace UnitSphereOrthogonalAction OrthogonalHausdorffImage OpenSubspaceMeasure
  HausdorffMeasure MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_sphere_hausdorff_invariant]: the orthogonal
    invariance used with 2.7.11(2) in Federer 3.2.13, p. 251,
    derived from the actual ambient Hausdorff preimage identity. *)
Theorem unit_sphere_hausdorff_invariant (R:realType) m
    (g:set_type (euclidean_orthogonal_group R m)):
  measure_pushforward (@unit_sphere_action R m g) (@unit_sphere_hausdorff_measure R m)=
    @unit_sphere_hausdorff_measure R m.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R m).
pose S:=euclidean_unit_sphere_space R m.
pose f:=hom_as_linear (orthogonal_element_map g).
have hf:is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) f:=
  orthogonal_element_orthogonal g.
apply:funext=>A; rewrite /measure_pushforward /unit_sphere_hausdorff_measure /open_subspace_measure.
have hTrace:set_val @` ((@unit_sphere_action R m g) @^-1` A)=
    f @^-1` (set_val @` A).
  apply/seteqP; split=>x.
  - move=>[u hu <-].
    exists (unit_sphere_action g u)=>//; by rewrite unit_sphere_action_value hom_as_linearE.
  - move=>[v hv hfv].
    have hx:@euclidean_unit_sphere_set R m x.
      have hV:@euclidean_unit_sphere_set R m (set_val v):=set_valP v.
      change (inner_norm (@euclidean_inner_productP R m) (set_val v)= 1) in hV.
      rewrite hfv in hV.
      by rewrite /euclidean_unit_sphere_set /= (orthogonal_map_norm
        (@euclidean_inner_productP R m) (@euclidean_inner_productP R m) hf) in hV *.
    pose u:S:=exist _ x (mem_set hx).
    have hAction:unit_sphere_action g u=v.
      apply:val_inj; change (f x=set_val v).
      exact:esym hfv.
    exists u; last by [].
    by rewrite /= hAction.
rewrite hTrace; exact:hausdorff_orthogonal_preimage hf.
Qed.
