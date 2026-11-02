(** Federer (1969), 3.1.13, p. 225:
    local finiteness of a function family means
    that one finite selection suffices throughout
    an open neighborhood of each domain point. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import NormDifferentialUP FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_norm_locally_finite_function_family]:
    the local finite expression for the sum
    u in Federer 3.1.13, p. 225.
    A neighborhood remains inside U, and
    every unselected indexed function is identically
    zero there. No convergence assumption occurs. *)
Definition is_norm_locally_finite_function_family (R : realType)
    (X : lmodType R) (Y : zmodType) (J : choiceType)
    (NX : X->R) (U : X->Prop) (I : J->Prop) (f : J->X->Y) :=
  forall a, U a -> exists O : X->Prop,
    O a /\ (forall x, O x -> U x) /\
    (forall x, O x -> norm_domain_interior NX O x) /\
    exists F : {fset J},
      (forall j, j \in F -> I j) /\
      (forall x, O x -> forall j, I j -> j \notin F -> f j x=0).

(** Source for [norm_locally_finite_active_family]:
    local finiteness implies finite active
    selections at each point, supporting the
    existence of u in Federer 3.1.13, p. 225. *)
Lemma norm_locally_finite_active_family (R : realType)
    (X : lmodType R) (Y : zmodType) (J : choiceType)
    (NX : X->R) (U : X->Prop) (I : J->Prop) (f : J->X->Y) :
  is_norm_locally_finite_function_family NX U I f ->
  finite_active_family_on U I f.
Proof.
move=>hloc x hx; have [O [hOx [_ [_ [F [hFI hF]]]]]] := hloc x hx.
exists F; split; first exact hFI; exact: hF x hOx.
Qed.
