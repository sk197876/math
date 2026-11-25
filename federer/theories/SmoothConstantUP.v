(** Federer (1969), 4.1.7, p. 356: actual
    constant smooth coefficient fields used in the
    original coordinate and current identities.
    The public law is independent of a construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smooth_constant_operator]: the
    original pointwise constant field, supporting
    Federer 4.1.7, p. 356. *)
Definition is_smooth_constant_operator (R:realType) (X Y E:lmodType R)
    (U:X->Prop) (ev:E->X->Y) (L:Hom Y E):Prop:=
  forall c x,U x->ev (L c) x=c.
