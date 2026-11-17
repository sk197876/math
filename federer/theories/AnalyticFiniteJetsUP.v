(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite prefixes of the actual derivative sequence.
    Their target uses the existing opaque finite-product
    space of 3.1.1(4), p. 210. The germ-to-product
    map is specified by every original derivative
    before its existence is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormedFamilyUP NormedFamilySealed
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermRing AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Prefix.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable m:nat.

(** Source for [analytic_finite_jet_space]: the existing
    abstract finite product of the original derivative
    spaces, supporting 3.4.8(5), p. 328, with
    the derivative sequence of 3.4.5, p. 319. *)
Definition analytic_finite_jet_space:lmodType R:=
  @NormedFamily.space R m (fun i:'I_m=>
    @ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).

(** Source for [analytic_finite_jet_coordinate]: the
    existing abstract projection to each original derivative
    space, supporting 3.4.8(5), p. 328. *)
Definition analytic_finite_jet_coordinate (i:'I_m):Hom analytic_finite_jet_space
  (@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)):=
  @NormedFamily.coordinate R m (fun i:'I_m=>
    @ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)) i.

(** Source for [analytic_finite_jet_norm]: the compatible
    sum norm of the existing abstract finite product,
    used only to prove finite-jet closedness for
    3.4.8(5), p. 328. *)
Definition analytic_finite_jet_norm:analytic_finite_jet_space->R:=
  @NormedFamily.norm R m (fun i:'I_m=>
    @ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
    (fun i:'I_m=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).

(** Source for [is_analytic_finite_jet_map]: every
    product coordinate equals the corresponding actual
    germ derivative from 3.4.5, p. 319, supporting
    the closedness proof for 3.4.8(5), p. 328.
    No continuity, finite-dimensionality or ideal conclusion
    is included among these membership-independent laws. *)
Definition is_analytic_finite_jet_map a
  (f:@analytic_germ_ring R X NX hNX a->analytic_finite_jet_space):Prop:=
  forall alpha i,analytic_finite_jet_coordinate i (f alpha) =
    @AnalyticGermJets.value R X NX hNX a i alpha.
End Prefix.
