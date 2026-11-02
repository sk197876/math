(** Federer (1969), 2.10.45, pp. 202–203: coordinate cubes supply the
    compact bounded sets used after the cube estimate. The coordinate
    inequalities are the rectangular-box laws of 2.7.16, p. 136. This file
    identifies those inequalities with the existing abstract box
    specification; it selects no new geometric object. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  OrthonormalFamilies EuclideanBoxUP CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_cube_laws]: supporting
    recognition of a coordinate cube as an m-dimensional
    cube in 2.10.45, p. 202, using the
    orthonormal-coordinate definition in 2.7.16, p. 136.
    The origin is supplied through its coordinate law;
    zero side length and zero dimension are permitted. *)
Lemma euclidean_coordinate_cube_laws (R : realType) m (origin : R_n R m) (a u : R) :
  (forall i, origin i=a) -> 0<=u ->
  @is_euclidean_rectangular_box R m origin (@coordinate_basis R m) (fun _=>u)
    [set x : inner_metric_space (@euclidean_inner_productP R m) | forall i, a<=x i<=a+u].
Proof.
move=> ho hu; constructor.
- by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
- by move=> i.
- move=> x; split=> hx i.
  + rewrite euclidean_inner_basis !ffunE ho.
    have /andP[hl hr] := hx i; apply/andP; split; lra.
  + have hh := hx i; rewrite euclidean_inner_basis !ffunE ho in hh.
    have /andP[hl hr] := hh; apply/andP; split; lra.
Qed.
