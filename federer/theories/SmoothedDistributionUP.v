(** Federer (1969), 4.1.2, p. 347: the
    original smoothed distribution is specified by its
    exact action on actual tests. Membership in the
    continuous dual is supplied by the target space,
    and existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smoothed_distribution]: the original equation
    T_epsilon(f)=T(Phi_epsilon*f), Federer 4.1.2,
    p. 347, expressed with the actual test
    smoothing operator and continuous-dual evaluation. *)
Definition is_smoothed_distribution (R:realType) (DT DD:lmodType R)
    (eD:Hom DD (Hom DT R^o)) (T:Hom DT R^o) (Q:Hom DT DT) (A:DD):Prop:=
  forall f,eD A f=T (Q f).

(** Source for [smoothed_distribution_unique]: the original
    action determines T_epsilon uniquely in Federer 4.1.2,
    p. 347. No function-space construction is exposed. *)
Theorem smoothed_distribution_unique (R:realType) (DT DD:lmodType R)
    (eD:Hom DD (Hom DT R^o)) (T:Hom DT R^o) (Q:Hom DT DT) (A B:DD):
  injective eD ->is_smoothed_distribution eD T Q A ->
  is_smoothed_distribution eD T Q B ->A=B.
Proof.
move=>hInjective hA hB; apply:hInjective; apply:hom_ext=>f.
by rewrite hA hB.
Qed.
