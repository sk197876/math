(** Federer (1969), 3.2.31, p. 269: supporting finite compact
    cover for the small-exterior rescaling argument. Independent
    cover, inverse, norm and local Lipschitz laws precede existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions LipschitzUP SmallExteriorMajorantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RescaledCoverLaws.
Variable R:realType.
Variables m v mu:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [is_compact_rescaled_cover]: supporting compact
    refinement of the rescaling neighborhoods in Federer 3.2.31,
    p. 269. Exact coverage and null overlaps retain the source
    mass. Actual symmetric majorants and unit Lipschitz laws are
    requirements on the witnesses, not new project axioms. *)
Record is_compact_rescaled_cover (G:X->Y) (D:X->Hom (R_n R m) (R_n R v))
    (K:set X) (epsilon:R) N (a:nat->X)
    (T U:nat->Hom (R_n R v) (R_n R v)) (C:nat->set X):Prop:={
  (** Source for [rescaled_cover_centers]: supporting centers of the
      local neighborhoods in Federer 3.2.31, p. 269. *)
  rescaled_cover_centers:forall i,(i<N)%N ->K (a i);
  (** Source for [rescaled_cover_compact]: supporting compact pieces
      for fibre measurability in Federer 3.2.31, p. 269. *)
  rescaled_cover_compact:forall i,(i<N)%N ->compact (C i);
  (** Source for [rescaled_cover_subsets]: supporting original-source
      restrictions in Federer 3.2.31, p. 269. *)
  rescaled_cover_subsets:forall i,(i<N)%N ->C i `<=` K;
  (** Source for [rescaled_cover_union]: supporting exact coverage for
      the integral sum in Federer 3.2.31, p. 269. *)
  rescaled_cover_union:(\bigcup_(i in [set i|(i<N)%N]) C i)=K;
  (** Source for [rescaled_cover_null_overlaps]: supporting exact
      source-mass summation in Federer 3.2.31, p. 269, by 2.1.3, p. 55. *)
  rescaled_cover_null_overlaps:forall i j,(i<N)%N ->(j<N)%N ->i!=j ->
    @euclidean_lebesgue_measure R m (C i `&` C j)=0;
  (** Source for [rescaled_cover_majorants]: the actual small symmetric
      automorphisms required in Federer 3.2.31, p. 269. *)
  rescaled_cover_majorants:forall i,(i<N)%N ->
    @is_small_exterior_majorant R m v mu (D (a i)) epsilon (T i) (U i);
  (** Source for [rescaled_cover_contractions]: supporting restriction
      Lip(t^-1 f|E)<=1 in Federer 3.2.31, p. 269. *)
  rescaled_cover_contractions:forall i,(i<N)%N ->
    @is_metric_lipschitz_bound R X Y (C i) (fun x=>U i (G x)) 1%R
}.
End RescaledCoverLaws.
