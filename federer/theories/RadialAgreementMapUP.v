(** Federer (1969), 4.1.15, p. 372: independent value law
    of G_r=f+Psi_r(g-f), before existence or regularity.
    The codomain is the ambient Euclidean space; the book
    does not assert G_r(U) contained in V. *)
From mathcomp Require Import all_boot all_order all_algebra
  boolp reals.
From Federer Require Import GrassmannAbbreviations RadialShrinkMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_radial_agreement_map]: the displayed
    definition of G_r in 4.1.15, p. 372, using the
    independently specified opaque radial map. No bound,
    convergence or support-coincidence assertion is assumed. *)
Definition is_radial_agreement_map (R:realType) (n nu:nat)
    (r:R) (hr:0<r) (f g G:R_n R n->R_n R nu):Prop :=
  forall x,G x=f x+@RadialShrinkMap.value R nu r hr (g x-f x).
Arguments is_radial_agreement_map {R n nu} r hr f g G.

(** Source for [radial_agreement_map_unique]: the original
    value formula for G_r in 4.1.15, p. 372,
    determines it on every point of the ambient source. *)
Theorem radial_agreement_map_unique (R:realType) (n nu:nat)
    (r:R) (hr:0<r) (f g G H:R_n R n->R_n R nu):
  is_radial_agreement_map r hr f g G ->
  is_radial_agreement_map r hr f g H ->G=H.
Proof.
move=>hG hH;apply:funext=>x.
exact:(eq_trans (hG x) (esym (hH x))).
Qed.
