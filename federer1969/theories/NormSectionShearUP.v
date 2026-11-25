(** Federer (1969), 3.1.18, p. 230: the two displayed target
    changes of coordinates. Their domain, class, inverse and
    differential laws are proved separately from these formulas. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_section_shear]: h=identity+p*p-psi p,
    the displayed target change in Federer 3.1.18, p. 230. *)
Definition norm_section_shear (R:realType) (Y V:lmodType R)
    (p:Hom Y V) (j:Hom V Y) (psi:V->Y) y := y+j (p y)-psi (p y).

(** Source for [norm_section_shear_inverse]: identity-p*p+psi p,
    the displayed inverse target change in Federer 3.1.18, p. 230. *)
Definition norm_section_shear_inverse (R:realType) (Y V:lmodType R)
    (p:Hom Y V) (j:Hom V Y) (psi:V->Y) y := y-j (p y)+psi (p y).
