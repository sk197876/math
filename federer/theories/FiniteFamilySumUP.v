(** Federer (1969), 3.1.13, p. 225:
    a locally finite sum is specified by its
    values on every finite set containing the
    active terms. This avoids imposing any
    convergence or completeness hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [is_finite_family_sum_on]:
    the sum u(x)=sum_s u_s(x) in
    Federer 3.1.13, p. 225.
    Any finite selection containing all nonzero
    summands at x has the prescribed value.
    The statement is restricted to the domain U. *)
Definition is_finite_family_sum_on (X : Type) (J : choiceType)
    (Y : zmodType) (U : X->Prop) (I : J->Prop)
    (f : J->X->Y) (g : X->Y) :=
  forall x, U x -> forall F : {fset J},
    (forall j, j \in F -> I j) ->
    (forall j, I j -> j \notin F -> f j x=0) ->
    g x=\sum_(j <- F) f j x.

(** Source for [finite_family_sum_selection_independent]:
    zero summands outside the active finite
    family do not change u(x), supporting
    Federer 3.1.13, p. 225. *)
Lemma finite_family_sum_selection_independent (J : choiceType) (Y : zmodType)
    (I : J->Prop) (f : J->Y) (F G : {fset J}) :
  (forall j, j \in F -> I j) ->
  (forall j, j \in G -> I j) ->
  (forall j, I j -> j \notin F -> f j=0) ->
  (forall j, I j -> j \notin G -> f j=0) ->
  \sum_(j <- F) f j=\sum_(j <- G) f j.
Proof.
move=> hFI hGI hF hG.
have hUI j : j \in F `|` G -> I j.
  rewrite in_fsetU=>/orP [hj|hj]; [exact: hFI j hj|exact: hGI j hj].
have hFU : \sum_(j <- F) f j=\sum_(j <- F `|` G) f j.
  apply: big_fset_incl; first exact: fsubsetUl.
  move=>j hj hn; exact: hF j (hUI j hj) hn.
have hGU : \sum_(j <- G) f j=\sum_(j <- F `|` G) f j.
  apply: big_fset_incl; first exact: fsubsetUr.
  move=>j hj hn; exact: hG j (hUI j hj) hn.
by rewrite hFU hGU.
Qed.

(** Source for [finite_family_sum_unique]:
    uniqueness of the locally finite sum in
    Federer 3.1.13, p. 225,
    wherever a finite active selection exists. *)
Theorem finite_family_sum_unique (X : Type) (J : choiceType) (Y : zmodType)
    (U : X->Prop) (I : J->Prop) (f : J->X->Y) (g h : X->Y) :
  (forall x, U x -> exists F : {fset J},
    (forall j, j \in F -> I j) /\
    (forall j, I j -> j \notin F -> f j x=0)) ->
  is_finite_family_sum_on U I f g ->
  is_finite_family_sum_on U I f h ->
  forall x, U x -> g x=h x.
Proof.
move=> hfin hg hh x hx; have [F [hFI hF]] := hfin x hx.
by rewrite (hg x hx F hFI hF) (hh x hx F hFI hF).
Qed.

(** Source for [finite_active_family_on]:
    finitely many summands suffice at each
    point of the domain, as in
    Federer 3.1.13, p. 225.
    Local finiteness will prove this condition. *)
Definition finite_active_family_on (X : Type) (J : choiceType)
    (Y : zmodType) (U : X->Prop) (I : J->Prop) (f : J->X->Y) :=
  forall x, U x -> exists F : {fset J},
    (forall j, j \in F -> I j) /\
    (forall j, I j -> j \notin F -> f j x=0).
