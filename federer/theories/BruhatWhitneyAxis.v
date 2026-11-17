(** Federer (1969), 3.4.10, p. 338:
    the actual z-axis in the cited polynomial surface.
    This notation is a local geometric witness, not
    a replacement for the sealed surface definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanBlockLinearMaps
  EuclideanThreeBlockCoordinates BruhatWhitneyPhysicalProjection BruhatWhitneyAuxiliaryEquation
  BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bruhat_whitney_axis]: the axis (0,0,b)
    used in the example cited by 3.4.10, p. 338. *)
Definition bruhat_whitney_axis (R:realType) (b:R):R_n R 3:=
  b*:@coordinate_basis R 3 ord_max.

(** Source for [bruhat_whitney_axis_coordinates]: the exact
    coordinates of this original axis, 3.4.10, p. 338. *)
Lemma bruhat_whitney_axis_coordinates (R:realType) (b:R):
  @bruhat_whitney_axis R b ord0=0 /\
  @bruhat_whitney_axis R b (Ordinal (isT:(1<3)%N))=0 /\
  @bruhat_whitney_axis R b ord_max=b.
Proof.
rewrite /bruhat_whitney_axis /coordinate_basis !ffunE /=.
change (b*0=0 /\b*0=0 /\b*1=b).
by rewrite mulr0 mulr1.
Qed.

(** Source for [bruhat_whitney_axis_membership]: every original
    axis point is on the actual surface, 3.4.10, p. 338. *)
Lemma bruhat_whitney_axis_membership (R:realType) (b:R):
  @BruhatWhitneySurface.set R (@bruhat_whitney_axis R b).
Proof.
apply/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R)).
rewrite (bruhat_whitney_axis_coordinates b).1
  (bruhat_whitney_axis_coordinates b).2.1;ring.
Qed.

(** Source for [bruhat_whitney_axis_prefix]: the physical
    and implicit coordinate prefixes agree at the original
    axis point, supporting 3.4.10, p. 338. *)
Lemma bruhat_whitney_axis_prefix (R:realType) (b:R):
  @bruhat_whitney_physical_projection R (@bruhat_whitney_axis R b)=
    @euclidean_first_block_map R 2 1 (@bruhat_whitney_auxiliary_point R b).
Proof.
apply/ffunP=>i;have hi:(i=ord0)\/(i=ord_max).
  case:i=>[i hi];case:i hi=>[|[|i]] hi.
  - left;exact:val_inj.
  - right;exact:val_inj.
  - by move:hi.
rewrite /bruhat_whitney_physical_projection /= ffunE.
case:hi=>->.
- rewrite eqxx euclidean_three_prefix_first
    (bruhat_whitney_auxiliary_point_coordinates b).1.
  change (@bruhat_whitney_axis R b ord0=0).
  exact:(bruhat_whitney_axis_coordinates b).1.
- rewrite /= euclidean_three_prefix_second
    (bruhat_whitney_auxiliary_point_coordinates b).2.1.
  change (@bruhat_whitney_axis R b ord_max=b).
  exact:(bruhat_whitney_axis_coordinates b).2.2.
Qed.
