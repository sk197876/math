(** Federer (1969), 3.2.20, p. 256: the approximate
    differential has an ambient linear representative agreeing on its
    actual tangent-cone domain, by the uniqueness laws of 3.2.16,
    p. 253. This is used only to prove finite norm existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP PartialFunctionUP MeasureUP
  MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_approximate_differential_linear_model]: supporting
    linear-representative consequence for the norm in Federer 3.2.20,
    p. 256, from the definition and uniqueness in 3.2.16,
    p. 253. Only agreement on actual partial-graph values is
    asserted; the representative is not part of the chosen differential's
    public domain and is not selected globally. *)
Theorem measure_approximate_differential_linear_model (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a
    (d : partial_function X Y) :
  is_measure mu -> is_measure_approximate_differential NY hNX mu m f a d ->
  exists D : Hom X Y, has_measure_approximate_differential NY hNX mu m f a D /\
    forall v w, partial_function_graph d v w -> D v=w.
Proof.
move=> hm hd; have [D hD] := hd.1.
exists D; split; first exact hD.
move=> v w hvw; have [hv [L [hL hLw]]] := (hd.2 v w).1 hvw.
have hEqual := @measure_approximate_linear_maps_agree_on_cone R X Y NX NY hNX hNY
  mu m f a D L hm hD hL v hv.
exact: (eq_trans hEqual hLw).
Qed.
