(** Federer (1969), 4.1.15, p. 372: existence of the
    map with the independently stated G_r value law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations RadialShrinkMapSealed
  RadialAgreementMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [radial_agreement_map_exists]: the displayed
    definition of G_r in 4.1.15, p. 372. A direct
    expression proves existence and is hidden by the seal. *)
Theorem radial_agreement_map_exists (R:realType) (n nu:nat)
    (r:R) (hr:0<r) (f g:R_n R n->R_n R nu):
  exists G,is_radial_agreement_map r hr f g G.
Proof.
exists (fun x=>f x+@RadialShrinkMap.value R nu r hr (g x-f x)).
by [].
Qed.
