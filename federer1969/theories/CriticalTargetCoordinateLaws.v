(** Federer (1969), 3.4.3, p. 317: consequences of the
    independently specified coordinates on the derivative range. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations CriticalTargetCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_target_coordinate_epimorphism]: L Df(a)
    is onto R^nu, supporting the joint inverse function step
    in 3.4.3, p. 317. This follows from the inverse and
    actual-range laws, without choosing another inverse. *)
Lemma critical_target_coordinate_epimorphism (R:realType) (X Y:lmodType R)
    (NY:Y->R) (D:Hom X Y) nu (L:Hom Y (R_n R nu)) (J:Hom (R_n R nu) Y):
  is_critical_target_coordinates NY D L J ->
  forall u,exists x,L (D x)=u.
Proof.
move=>h u.
have [x hx]:=(critical_target_coordinates_range h (J u)).2 (ex_intro _ u erefl).
exists x;by rewrite hx (critical_target_coordinates_inverse h).
Qed.

(** Source for [critical_target_coordinate_kernel]: ker(L Df(a))
    equals ker Df(a), the equality used in the second paragraph
    of 3.4.3, p. 317. Injectivity is required only on
    the actual differential range, not on the ambient target. *)
Lemma critical_target_coordinate_kernel (R:realType) (X Y:lmodType R)
    (NY:Y->R) (D:Hom X Y) nu (L:Hom Y (R_n R nu)) (J:Hom (R_n R nu) Y):
  is_critical_target_coordinates NY D L J ->
  forall x,L (D x)=0 <->D x=0.
Proof.
move=>h x;split;last by move=>->;rewrite linear0.
move=>hZero.
have [u hu]:=(critical_target_coordinates_range h (D x)).1 (ex_intro _ x erefl).
have hU:u=0.
  have hh:=congr1 L hu.
  by rewrite (critical_target_coordinates_inverse h) hZero in hh.
by rewrite -hu hU linear0.
Qed.
