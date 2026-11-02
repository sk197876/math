(** Federer (1969), 3.2.33, p. 270: measurability and
    product coordinates of the original open unit cube. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanOneCoordinate OpenRestrictionZeroExtensionMeasurable TopologicalBorel
  EuclideanOpenUnitCube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_unit_cube_borel]: W is Borel,
    supporting the standing measurable-source hypothesis of
    3.2.32 for the example in 3.2.33, p. 270.
    The explicit norm interior balls prove openness first. *)
Lemma euclidean_open_unit_cube_borel (R:realType) n:
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) (@euclidean_open_unit_cube R n).
Proof.
apply:open_borel_set; apply:inner_norm_domain_open=>x hx.
exact:(euclidean_open_unit_cube_interior hx).
Qed.

(** Source for [euclidean_open_unit_cube_split]: W is the
    product of its coordinate cubes, supporting the source
    measure and fibre identities in 3.2.33, p. 270. *)
Lemma euclidean_open_unit_cube_split (R:realType) a b (x:R_n R (a+b)):
  euclidean_open_unit_cube x <->
  euclidean_open_unit_cube (@euclidean_first_block R a b x) /\
  euclidean_open_unit_cube (@euclidean_last_block R a b x).
Proof.
have h:=euclidean_open_unit_cube_join (@euclidean_first_block R a b x) (@euclidean_last_block R a b x).
change (euclidean_open_unit_cube (euclidean_block_join (@euclidean_block_split R a b x)) <->euclidean_open_unit_cube (@euclidean_first_block R a b x) /\
  euclidean_open_unit_cube (@euclidean_last_block R a b x)) in h.
by rewrite euclidean_block_splitK in h.
Qed.

(** Source for [euclidean_open_unit_cube_one]: the one-dimensional
    factor is the actual scalar interval T in the construction
    of Federer 3.2.33, p. 270, including its exact open endpoints. *)
Lemma euclidean_open_unit_cube_one (R:realType) (x:R_n R 1):
  euclidean_open_unit_cube x <->(0<euclidean_one_project x<1).
Proof.
split; first by move=>h; exact:(h ord0).
by move=>h i; rewrite (ord1 i); exact h.
Qed.
