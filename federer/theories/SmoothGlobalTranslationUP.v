(** Federer (1969), 4.1.1, p. 346: globally
    translated test functions in the Taylor difference
    quotient. These independent laws specify translation
    of the original smooth functions. *)
From mathcomp Require Import all_boot all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smooth_global_translation]: the translated
    function has value phi(x+c), supporting the
    displayed difference quotient in Federer 4.1.1,
    p. 346. *)
Definition is_smooth_global_translation (R:realType) (X Y E:lmodType R)
    (ev:E->X->Y) (c:X) (L:Hom E E):=
  forall f x,ev (L f) x=ev f (x+c).
