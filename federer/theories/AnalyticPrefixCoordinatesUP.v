(** Federer (1969), 3.4.8(1), p. 326:
    the original projections onto the first coordinates
    are specified by their coordinate equations. The
    auxiliary inclusion is specified by its basis values.
    These independent laws precede existence and sealing. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_analytic_prefix_projection]: the exact
    printed equation p_j(x)=(omega_1(x),...,omega_j(x)),
    3.4.8(1), p. 326, including the empty coordinate
    map. Natural indices start at zero. *)
Definition is_analytic_prefix_projection (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N) (P:Hom X (R_n R j)):Prop:=
  forall x i,P x i=omega (widen_ord hjn i) x.

(** Source for [is_analytic_prefix_section]: the original
    basis vectors give an auxiliary section of p_j,
    supporting the coordinate germ subring in 3.4.8(1),(5),
    pp. 326, 328. Its independent laws state its
    values on the original coordinate basis. *)
Definition is_analytic_prefix_section (R:realType) (X:lmodType R) n
    (e:'I_n->X) j (hjn:(j<=n)%N) (S:Hom (R_n R j) X):Prop:=
  forall i,S (@coordinate_basis R j i)=e (widen_ord hjn i).
