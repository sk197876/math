(** Federer (1969), 4.1.25, p. 383: the
    full-fibre vector sum defines a partial function.
    Reuse the already proved uniqueness of the finite
    vector sum, independently of its eventual measurable
    and summability properties. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading PartialFunctionUP CurrentAreaFibreSumUP
  CurrentAreaFibreDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_fibre_density_exists]:
    existence of the target partial density defined by
    the original full-fibre formula in Federer 4.1.25,
    p. 383. The graph is independently specified;
    this proof merely realizes that graph. *)
Theorem current_area_fibre_density_exists (R : realType)
    (h2 : (1+1 : R) != 0) (X : choiceType) n m
    (f : X -> R_n R n)
    (u : partial_function X (exterior_power (R_n R n) m)) :
  exists eta : partial_function (R_n R n) (exterior_power (R_n R n) m),
    is_current_area_fibre_density f u eta.
Proof.
have hUnique y a b :
    @is_current_area_fibre_sum R X n m f u y a ->
    @is_current_area_fibre_sum R X n m f u y b -> a = b.
  move=> hA hB.
  exact: (@current_area_fibre_sum_unique R X n m f u h2 y a b hA hB).
exists (@Build_partial_function (R_n R n) (exterior_power (R_n R n) m)
  (@is_current_area_fibre_sum R X n m f u) hUnique).
by move=> y v; split.
Qed.
