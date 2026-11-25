(** Federer (1969), 3.2.38, pp. 274--275: independent laws
    for a finite source cube cover split by a compact good-point core. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanCoordinateCubeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_core_cube_cover]: supporting specification
    of the finite F/G decomposition in Federer 3.2.38, pp. 274--275.
    The scalar Lusin-core proof also records small mass of good cubes
    outside the compact core. The bad parents are subsequently
    subdivided by the proved side-r estimate. Existence, null faces
    and all mass bounds are proved from actual coordinate grids. *)
Record is_compact_core_cube_cover (R:realType) m (G B:finType)
    (C E:set (inner_metric_space (@euclidean_inner_productP R m))) (h e:R)
    (aG:G->R_n R m) (aB:B->R_n R m)
    (QG:G->set (inner_metric_space (@euclidean_inner_productP R m)))
    (QB:B->set (inner_metric_space (@euclidean_inner_productP R m))):Prop:={
  (** Source for [core_cover_good_cube]: side-h good source cubes,
      Federer 3.2.38, p. 274. *)
  core_cover_good_cube:forall i,is_euclidean_coordinate_cube (aG i) h (QG i);
  (** Source for [core_cover_bad_cube]: side-h bad parent cubes,
      Federer 3.2.38, p. 274, before subdivision. *)
  core_cover_bad_cube:forall i,is_euclidean_coordinate_cube (aB i) h (QB i);
  (** Source for [core_cover_source]: actual original source cover,
      Federer 3.2.38, pp. 274--275. *)
  core_cover_source:C `<=` (\bigcup_i QG i) `|` (\bigcup_i QB i);
  (** Source for [core_cover_good_meets]: each good cube meets E,
      Federer 3.2.38, p. 274. *)
  core_cover_good_meets:forall i,(QG i `&` E)!=set0;
  (** Source for [core_cover_bad_avoids]: bad parents miss E,
      Federer 3.2.38, p. 274. *)
  core_cover_bad_avoids:forall i,(QB i `&` E)=set0;
  (** Source for [core_cover_good_null_overlap]: actual null faces
      in the good-cube sum, Federer 3.2.38, p. 275. *)
  core_cover_good_null_overlap:forall i j,i!=j ->
    @euclidean_lebesgue_measure R m (QG i `&` QG j)=0%E;
  (** Source for [core_cover_bad_null_overlap]: actual null faces
      in the bad-parent sum, Federer 3.2.38, p. 275. *)
  core_cover_bad_null_overlap:forall i j,i!=j ->
    @euclidean_lebesgue_measure R m (QB i `&` QB j)=0%E;
  (** Source for [core_cover_good_outside]: compact-core variant of
      the outside-source error in Federer 3.2.38, p. 275. *)
  core_cover_good_outside:(@euclidean_lebesgue_measure R m ((\bigcup_i QG i) `\` E)<=e%:E)%E;
  (** Source for [core_cover_bad_mass]: the missing-core and
      outside-source mass bound, Federer 3.2.38, p. 275. *)
  core_cover_bad_mass:(@euclidean_lebesgue_measure R m (\bigcup_i QB i)<=(2*e)%R%:E)%E;
  (** Source for [core_cover_good_mass]: the total good-cube
      source mass bound, Federer 3.2.38, p. 275. *)
  core_cover_good_mass:(@euclidean_lebesgue_measure R m (\bigcup_i QG i)<=
    @euclidean_lebesgue_measure R m C+e%:E)%E
}.
