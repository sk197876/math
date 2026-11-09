(** Federer (1969), 3.4.5, p. 321: existence and
    uniqueness of the concrete cubic surface used for
    the local/global distinction; see Cartan (1957), p. 97. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations FlatExponentialSealed CartanSurfaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_flat_surface_exists]: the explicit
    equation cited at 3.4.5, p. 321, defines an
    actual set with the independent membership law. *)
Theorem cartan_flat_surface_exists (R:realType):exists S:set (R_n R 3),is_cartan_flat_surface S.
Proof.
exists (fun v:R_n R 3=>v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)=
  (v ord0)^+3*FlatExponential.value (1-v ord_max));by constructor.
Qed.

(** Source for [cartan_flat_surface_unique]: the membership
    equation determines the whole actual set, supporting
    the original distinction in 3.4.5, p. 321. *)
Theorem cartan_flat_surface_unique (R:realType) (S T:set (R_n R 3)):
  is_cartan_flat_surface S ->is_cartan_flat_surface T ->S=T.
Proof.
move=>hS hT;apply/seteqP;split=>v hv.
- apply/(cartan_surface_membership hT);exact:(cartan_surface_membership hS v).1 hv.
- apply/(cartan_surface_membership hS);exact:(cartan_surface_membership hT v).1 hv.
Qed.
