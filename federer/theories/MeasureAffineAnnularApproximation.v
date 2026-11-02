(** Federer (1969), 3.2.16, p. 253:
    the affine remainder tends to zero on
    the corrected annular set. The actual partial
    graph and the erratum's atomic base value
    are preserved throughout the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionExtensionUP MeasureUP
  RelativeDifferentialUP ExtendedRealReciprocalBounds
  MeasureApproximateAffineUP MeasureApproximateAffinePositiveAtom
  MetricDensityAnnularRadii ShrinkingRadiusSelectionUP
  NormAnnularSetUP NormAnnularSetGeometry NormAnnularOmissionDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_affine_annular_good_sets]:
    the sets S_i in Federer 3.2.16,
    p. 253. The natural index n stands
    for the book's positive index i=n+1. *)
Definition measure_affine_annular_good_sets (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (f : partial_function X Y) a eta (D : Hom X Y) (n : nat) :=
  measure_affine_approximation_set NX NY f a eta D ((n.+1%:R : R)^-1).

(** Source for [measure_affine_annular_first_order]:
    relative first-order approximation on T,
    or T union {a} at positive atoms,
    Federer 3.2.16, p. 253; erratum p. 5,
    line 32. A total extension is auxiliary
    and is used only at actual graph points. *)
Theorem measure_affine_annular_first_order (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a eta (D : Hom X Y)
    (rho : nat -> R) (T : set X) (g : X -> Y) :
  is_measure mu ->
  has_measure_approximate_affine_criterion NY hNX mu m f a eta D ->
  is_shrinking_radius_selection
    (@metric_density_annular_radius_property R (real_norm_metric_space hNX) mu m
      (measure_affine_annular_good_sets NX NY f a eta D) a) rho ->
  is_norm_annular_set NX (measure_affine_annular_good_sets NX NY f a eta D) a rho T ->
  is_partial_function_total_extension f g ->
  has_relative_first_order_approximation NX NY (partial_function_domain f)
    (norm_annular_corrected_set mu a T) g a eta D.
Proof.
move=> hm hCrit hR hT hExt.
have hnotA := norm_annular_set_excludes_center hNX hR hT.
have hAtom : (0<mu [set a])%E -> partial_function_graph f a eta.
  move=> hA; exact: (@measure_affine_positive_atom_value R X Y NX NY hNX hNY mu m f a eta D hm hA hCrit).
split; first exact hCrit.1.
split.
- move=> [ha|[_ ha]]; first by case: (hnotA ha).
  exact: hExt _ _ (hAtom ha).
split.
- exists (rho 0%N); split; first exact: shrinking_radius_positive hR 0%N.
  move=> x [hx|[-> ha]] _.
  + have [n [hn _]] := (hT x).1 hx.
    have [y [hfy _]] := hn; by exists y.
  + by exists eta; exact: hAtom.
- move=> e he.
  have [J hJe] := positive_reciprocal_nat_small he.
  exists (rho J); split; first exact: shrinking_radius_positive hR J.
  move=> x hx hp hsmall.
  have hxT : T x.
    case: hx=> [hx|[heq _]]; first exact hx.
    rewrite heq subrr (real_seminorm_zero hNX.1) in hp.
    by rewrite ltxx in hp.
  have [n [hSn [houter hinner]]] := (hT x).1 hxT.
  have hJn := norm_annular_index_near_center hR hinner hsmall.
  have [y [hfy herr]] := hSn.
  have hgxy := hExt x y hfy.
  rewrite hgxy.
  apply: (le_trans herr _); apply: ler_wpM2r; first exact: ltW hp.
  apply: (le_trans _ (ltW hJe)).
  have hn : 0<(n.+1%:R : R) by rewrite ltr0n.
  have hJ : 0<(J.+1%:R : R) by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hn hJ) ler_nat.
Qed.
