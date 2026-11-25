(** Federer (1969), 3.4.10, p. 338:
    existence and uniqueness for the surface
    cited to Bruhat and Whitney, section 11(c),
    p. 159, by its original equation alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations BruhatWhitneySurfaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_surface_exists]: the
    explicit equation in section 11(c), p. 159,
    of the source cited by 3.4.10,
    p. 338, supplies a membership-law witness. *)
Theorem bruhat_whitney_surface_exists (R:realType):
  exists S:set (R_n R 3),is_bruhat_whitney_surface S.
Proof.
exists (fun v:R_n R 3=>v (Ordinal (isT:(1<3)%N))*v ord_max*
  ((v ord0)^+2-v ord_max*(v (Ordinal (isT:(1<3)%N)))^+2)+(v ord0)^+4=0).
by constructor.
Qed.

(** Source for [bruhat_whitney_surface_unique]: the
    original membership equation uniquely determines the
    surface used in 3.4.10, p. 338. *)
Theorem bruhat_whitney_surface_unique (R:realType) (S T:set (R_n R 3)):
  is_bruhat_whitney_surface S ->is_bruhat_whitney_surface T ->S=T.
Proof.
move=>hS hT;apply/seteqP;split=>v hv.
- apply/(bruhat_whitney_surface_membership hT);exact:(bruhat_whitney_surface_membership hS v).1 hv.
- apply/(bruhat_whitney_surface_membership hS);exact:(bruhat_whitney_surface_membership hT v).1 hv.
Qed.
