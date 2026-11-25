(** Federer (1969), 4.1.2, p. 347: the distribution
    smoothing family is independently specified by its test actions
    at every positive scale. Nonpositive values are unconstrained. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom SmoothedDistributionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smoothed_distribution_family]: the displayed original
    formula T_epsilon(f)=T(Phi_epsilon*f), Federer 4.1.2, p. 347,
    simultaneously for all positive epsilon. *)
Definition is_smoothed_distribution_family (R:realType) (DT DD:lmodType R)
    (eD:Hom DD (Hom DT R^o)) (T:Hom DT R^o)
    (Q:R->Hom DT DT) (A:R->DD):Prop:=
  forall e:R,0<e ->is_smoothed_distribution eD T (Q e) (A e).
