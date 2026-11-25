(** Federer (1969), 4.1.25, p. 383: the
    target density is specified by its exact full-fibre
    vector sum. Existence of this partial function and
    its almost-everywhere domain are separate assertions;
    no value is prescribed outside the original domain. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading PartialFunctionUP PartialFunctionExtensionality
  CurrentAreaFibreSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_current_area_fibre_density]: the
    density displayed in Federer 4.1.25, p. 383,
    with precisely the domain on which its original
    full-fibre vector sum exists. *)
Definition is_current_area_fibre_density (R : realType) (X : choiceType)
    n m (f : X -> R_n R n)
    (u : partial_function X (exterior_power (R_n R n) m))
    (eta : partial_function (R_n R n) (exterior_power (R_n R n) m)) : Prop :=
  forall y v, partial_function_graph eta y v <->
    @is_current_area_fibre_sum R X n m f u y v.

(** Source for [current_area_fibre_density_unique]:
    the original full-fibre formula determines the
    target partial density uniquely, supporting Federer
    4.1.25, p. 383. *)
Theorem current_area_fibre_density_unique (R : realType) (X : choiceType)
    n m f u (eta zeta : partial_function (R_n R n) (exterior_power (R_n R n) m)) :
  @is_current_area_fibre_density R X n m f u eta ->
  @is_current_area_fibre_density R X n m f u zeta -> eta = zeta.
Proof.
move=> hEta hZeta; apply: partial_function_graph_extensionality => y v.
by rewrite (hEta y v) (hZeta y v).
Qed.
