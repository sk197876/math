(** Federer (1969), 3.1.11, p. 220:
    intrinsic higher ordinary derivatives for a real
    source. Each successive derivative differentiates a
    representative only near an interior point of the
    exact preceding derivative domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom NormDifferentialUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_coefficient_linear_map]:
    a real-source differential with coefficient v sends
    t to t v, Federer 3.1.11, p. 220. *)
Definition scalar_coefficient_linear_map (R : realType) (Y : lmodType R)
    (v : Y) : Hom R^o Y.
Proof.
apply: (@HomMap R R^o Y (fun t=>t*:v)).
apply/asboolP=> c t s.
by change ((c*t+s)*:v=c*:(t*:v)+s*:v); rewrite scalerDl scalerA.
Defined.

(** Source for [has_norm_higher_curve_derivative]:
    the recursion f^(0)=f and f^(k+1)=(f^(k))'
    in Federer 3.1.11, p. 220. The interior
    requirement preserves the book's domain convention for
    higher differentiability, rather than differentiating a
    chosen value outside the preceding domain. *)
Fixpoint has_norm_higher_curve_derivative (R : realType) (Y : lmodType R)
    (NY : Y->R) (A : R->Prop) (f : R->Y) (k : nat) : R->Y->Prop :=
  match k with
  | 0%N=>fun a v=>A a /\ v=f a
  | j.+1=>fun a v=>exists g : R->Y,
      (forall x w, @has_norm_higher_curve_derivative R Y NY A f j x w -> g x=w) /\
      norm_domain_interior (fun t : R^o=>`|t|)
        (fun x=>exists w, @has_norm_higher_curve_derivative R Y NY A f j x w) a /\
      has_normed_curve_derivative NY g a v
  end.
