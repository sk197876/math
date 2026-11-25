(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: the original dual complex basis gives actual
    coordinate germs. Apply the published dual-space correction
    at book p. 326 line 3. Representative equations precede existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_holomorphic_coordinate_germs]: every actual
    representative of an original complex coordinate gives its
    original germ gamma_j, extending corrected 3.4.8(1), p. 326.
    No image, ideal depth or dimension conclusion is included. *)
Definition is_holomorphic_coordinate_germs (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (gamma:'I_n->@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0):Prop:=
  forall j (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0),
    (forall x,holomorphic_representative_value f x=omega j x) ->holomorphic_germ f=gamma j.
