(** Federer (1969), 2.7.16, printed p. 139, example (6), for R^n: "Since the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n), there exists
    a unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1. For every transitive action A of O(n) on a
    homogeneous space X, and each x in X, the measure (A^x)_# theta_n over X
    is invariant with [(A^x)_# theta_n] X = 1. In particular we thus obtain
    the O(n) invariant measures theta_{n,m} over O(n, m), theta*_{n,m} over
    O*(n, m), gamma_{n,m} over G(n, m)." This module specialises
    OrthogonalGroupHaarMeasure.v, OrthogonalInjectionSpaces.v and
    GrassmannHomogeneousSpace.v to V = R^n and U = R^m, with the inner
    product of 1.7.1, p. 28 (euclidean_inner_product) and the standard
    basis, and identifies the spaces with the sets of Chapter 1: O(n, m) and
    O(n) of 1.7.2, p. 28 (FedererOrthogonal.O, FedererOrthogonal.O_group),
    O*(n, m) of 1.7.4, p. 30 (O_star), and G(n, m) of 1.6.2, p. 24
    (FedererEuclideanGrassmann.G). For m <= n the spaces are nonempty, and
    each carries exactly one O(n) invariant measure with total measure 1.
     The local erratum has no entry
    for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric LinearBasis TensorUP Hom HomInner
  OrthogonalMaps OrthonormalFamilies AdjointUP Adjoint GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates OrthogonalEuclidean CoordinateProjection
  OrthonormalFrameMap IsotropyGroupTopology TopologicalGroupUP HomogeneousSpaceUP
  MeasurePushforward HaarIntegralUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures OrthogonalInjectionSpaces GrassmannHomogeneousSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Euclidean.
Variable R : realType.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbm := (@coordinate_basisP R m).

(** Source for [euclidean_orthogonal_group]: "the orthogonal group
    O(n)", Federer 2.7.16, p. 139, as a subset of the linear group of
    R^n with the topology of Hom(R^n, R^n). Definition. *)
Definition euclidean_orthogonal_group := orthogonal_group hBn hbn.

(** Source for [euclidean_orthogonal_groupE]: the members of O(n) are
    the members of O(n) = O(n, n) of Federer 1.7.2, p. 28
    (FedererOrthogonal.O_group). Supporting lemma. *)
Lemma euclidean_orthogonal_groupE (g : set_type (linear_group hBn hbn)) :
  euclidean_orthogonal_group g <-> @FedererOrthogonal.O_group R n (hom_as_linear (set_val g : Hom _ _)).
Proof. by []. Qed.

(** Source for [euclidean_orthogonal_injections]: "O(n, m)", Federer
    2.7.16, p. 139, as a subset of Hom(R^m, R^n). Definition. *)
Definition euclidean_orthogonal_injections := orthogonal_injections hBm hBn hbm.

(** Source for [euclidean_orthogonal_injectionsE]: the members of
    O(n, m) are those of FedererOrthogonal.O n m, Federer 1.7.2, p. 28.
    Supporting lemma. *)
Lemma euclidean_orthogonal_injectionsE f :
  euclidean_orthogonal_injections f <-> @FedererOrthogonal.O R n m (hom_as_linear f).
Proof. by []. Qed.

(** Source for [euclidean_orthogonal_projections]: "O*(n, m)", Federer
    2.7.16, p. 139, as a subset of Hom(R^n, R^m). Definition. *)
Definition euclidean_orthogonal_projections := orthogonal_projections hBm hBn hbn.

(** Source for [euclidean_orthogonal_projectionsE]: the members of
    O*(n, m) are those of O_star, "O*(n, m) = {f* : f in O(n, m)}",
    Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma euclidean_orthogonal_projectionsE p :
  euclidean_orthogonal_projections p <-> @O_star R n m (hom_as_linear p).
Proof. exact: iff_sym (O_star_projection _). Qed.

(** Source for [euclidean_grassmann_space]: "G(n, m)", Federer 2.7.16,
    p. 139, the set FedererEuclideanGrassmann.G n m of 1.6.2, p. 24,
    with the topology of GrassmannHomogeneousSpace.v. Definition. *)
Definition euclidean_grassmann_space := grassmann_space hBm hBn hbm hbn.

(** Source for [euclidean_grassmann_spaceE]: the points of G(n, m) are
    the members of FedererEuclideanGrassmann.G n m, Federer 1.6.2,
    p. 24. Supporting lemma. *)
Lemma euclidean_grassmann_spaceE : euclidean_grassmann_space = FedererEuclideanGrassmann.G R n m :> Type.
Proof. by []. Qed.

(** Source for [euclidean_orthogonal_injection_exists]: O(n, m) is
    nonempty for m <= n, Federer 1.7.2, p. 28: e_i |-> e_i is an
    orthogonal injection of R^m into R^n. Supporting lemma. *)
Lemma euclidean_orthogonal_injection_exists :
  (m <= n)%N -> exists f : {linear R_n R m -> R_n R n}, @FedererOrthogonal.O R n m f.
Proof.
move=> hmn.
pose e (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i == widen_ord hmn j) = (i == j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he : orthonormal_family (@euclidean_inner_product R n) e.
  move=> i j; rewrite /e euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
have [f [hf _]] := orthonormal_frame_map_exists hBn he.
by exists f.
Qed.

Variables (mulS : euclidean_orthogonal_group -> euclidean_orthogonal_group -> euclidean_orthogonal_group)
  (invS : euclidean_orthogonal_group -> euclidean_orthogonal_group) (eS : euclidean_orthogonal_group).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) euclidean_orthogonal_group mulS invS eS.

(** Source for [euclidean_theta_exists_unique]: "there exists a unique
    left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1", Federer 2.7.16, p. 139. Direct formalisation for
    R^n. *)
Theorem euclidean_theta_exists_unique :
  exists theta : set euclidean_orthogonal_group -> \bar R,
    [/\ is_left_haar_measure mulS theta, is_right_haar_measure mulS invS theta,
      theta [set: euclidean_orthogonal_group] = 1%E &
      forall psi, is_left_haar_measure mulS psi \/ is_right_haar_measure mulS invS psi ->
        psi [set: euclidean_orthogonal_group] = 1%E -> psi = theta].
Proof. exact: orthogonal_group_unique_haar_measure hS. Qed.

(** Source for [euclidean_orbit_invariant_measure]: "For every
    transitive action A of O(n) on a homogeneous space X, and each x in
    X, the measure (A^x)_# theta_n over X is invariant with
    [(A^x)_# theta_n] X = 1", Federer 2.7.16, p. 139. Direct
    formalisation for R^n; X is assumed Hausdorff. *)
Theorem euclidean_orbit_invariant_measure (X : topologicalType)
    (A : euclidean_orthogonal_group -> X -> X) (theta : set euclidean_orthogonal_group -> \bar R)
    (x : X) :
  is_homogeneous_space mulS A -> hausdorff_space X -> is_normalised_haar_measure mulS theta ->
  is_normalised_invariant_measure A (measure_pushforward (orbit_map A x) theta).
Proof. exact: (orthogonal_orbit_invariant_measure hS x). Qed.

Hypothesis hmn : (m <= n)%N.

(** Source for [euclidean_theta_nm_exists_unique]: "the O(n) invariant
    measure theta_{n,m} over O(n, m)", Federer 2.7.16, p. 139, for
    m <= n: there is exactly one O(n) invariant measure over O(n, m)
    with total measure 1, for the action A(g, f) = g o f, and it equals
    (A^f)_# theta_n for every f in O(n, m). Direct formalisation. *)
Theorem euclidean_theta_nm_exists_unique :
  exists phi : set (set_type euclidean_orthogonal_injections) -> \bar R,
    [/\ is_normalised_invariant_measure (orthogonal_injection_action hBm hBn hbm hbn) phi,
      forall psi, is_normalised_invariant_measure (orthogonal_injection_action hBm hBn hbm hbn) psi ->
        psi = phi &
      forall theta f, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map (orthogonal_injection_action hBm hBn hbm hbn) f) theta = phi].
Proof.
have [f hf] := euclidean_orthogonal_injection_exists hmn.
exact: (orthogonal_injections_invariant_measure hS (orthogonal_injection_of hBm hBn hbm hf)).
Qed.

(** Source for [euclidean_theta_star_nm_exists_unique]: "the O(n)
    invariant measure theta*_{n,m} over O*(n, m)", Federer 2.7.16,
    p. 139, for m <= n: there is exactly one O(n) invariant measure over
    O*(n, m) with total measure 1, for the action A(g, p) = p o g^{-1},
    and it equals (A^p)_# theta_n for every p in O*(n, m). Direct
    formalisation; f* is a point of O*(n, m) for f in O(n, m). *)
Theorem euclidean_theta_star_nm_exists_unique :
  exists phi : set (set_type euclidean_orthogonal_projections) -> \bar R,
    [/\ is_normalised_invariant_measure (orthogonal_projection_action hBm hBn hbn hS) phi,
      forall psi, is_normalised_invariant_measure (orthogonal_projection_action hBm hBn hbn hS) psi ->
        psi = phi &
      forall theta p, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map (orthogonal_projection_action hBm hBn hbn hS) p) theta = phi].
Proof.
have [f hf] := euclidean_orthogonal_injection_exists hmn.
have hp : is_orthogonal_projection (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    (inner_adjoint hBm hBn hbm f).
  by exists f; split; [exact: hf|exact: inner_adjointP].
exact: (orthogonal_projections_invariant_measure hbm hS (orthogonal_projection_of hBm hBn hbn hp)).
Qed.

(** Source for [euclidean_gamma_nm_exists_unique]: "the O(n) invariant
    measure gamma_{n,m} over G(n, m)", Federer 2.7.16, p. 139, for
    m <= n: there is exactly one O(n) invariant measure over G(n, m)
    with total measure 1, for the action A(g, W) = g[W], and it equals
    (A^W)_# theta_n for every W in G(n, m). Direct formalisation; the
    image of a member of O(n, m) is a point of G(n, m). *)
Theorem euclidean_gamma_nm_exists_unique :
  exists phi : set euclidean_grassmann_space -> \bar R,
    [/\ is_normalised_invariant_measure (grassmann_action hBm hBn hbm hbn) phi,
      forall psi, is_normalised_invariant_measure (grassmann_action hBm hBn hbm hbn) psi -> psi = phi &
      forall theta W, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map (grassmann_action hBm hBn hbm hbn) W) theta = phi].
Proof.
have [f hf] := euclidean_orthogonal_injection_exists hmn.
have hfi : injective f := orthogonal_map_injective hBm hBn hf.
exact: (grassmann_invariant_measure hS (linear_image_grassmann hbm hfi : euclidean_grassmann_space)).
Qed.

End Euclidean.

Arguments euclidean_orthogonal_group R n _ : clear implicits.
Arguments euclidean_orthogonal_injections R n m _ : clear implicits.
Arguments euclidean_orthogonal_projections R n m _ : clear implicits.
