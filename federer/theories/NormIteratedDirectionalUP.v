(** Federer (1969), 3.1.11, p. 223: recursive partial
    derivatives, first stated for a finite sequence of fixed directions.
    Substituting coordinate vectors gives the printed D_nu recursion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_line_domain]: the two-sided coordinate
    interval on which the quotient in 3.1.1, p. 211, is
    defined; used at each step of the recursion in 3.1.11,
    p. 223. It includes the base point itself. *)
Definition norm_line_domain (R : realType) (X : lmodType R)
    (A : X->Prop) (a v : X) :=
  exists r : R, 0<r /\ forall t, `|t|<r -> A (a+t*:v).

(** Source for [has_norm_line_derivative]: the limit of the
    quotient along a fixed direction, with its actual function
    domain, used for Federer 3.1.11, p. 223. *)
Definition has_norm_line_derivative (R : realType) (X Y : lmodType R)
    (NY : Y->R) (A : X->Prop) (f : X->Y) (a v : X) y :=
  norm_line_domain A a v /\
    punctured_norm_limit NY (fun t=>t^-1*:(f (a+t*:v)-f a)) y.

(** Source for [has_norm_iterated_directional]: the recursion
    D_(v1,...,vk)f=D_v1 D_(v2,...,vk)f, specializing to
    the displayed coordinate recursion in Federer 3.1.11, p. 223.
    Each step differentiates on the exact domain of the preceding
    graph. Total representatives have no specified values outside
    that domain. The empty sequence is the original function. *)
Fixpoint has_norm_iterated_directional (R : realType) (X Y : lmodType R)
    (NY : Y->R) (A : X->Prop) (f : X->Y) (s : seq X) : X->Y->Prop :=
  if s is v::s' then fun a y=>
    exists g : X->Y,
      (forall x z, has_norm_iterated_directional NY A f s' x z -> g x=z) /\
      has_norm_line_derivative NY
        (fun x=>exists z, has_norm_iterated_directional NY A f s' x z) g a v y
  else fun a y=>A a /\ y=f a.
