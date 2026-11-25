(** Federer (1969), 3.1.11, pp. 219–220,
    used in 3.1.13, p. 225:
    differentiability classes are local on open domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_local]:
    the continuity and open-domain convention of
    Federer 3.1.1, p. 210, applied
    locally as required in 3.1.13, p. 225. *)
Theorem norm_class_zero_local (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (A : X->Prop) (f : X->Y) :
  (forall a, A a -> exists O : X->Prop,
    O a /\ (forall x, O x -> A x) /\ norm_class_zero NX NY O f) ->
  norm_class_zero NX NY A f.
Proof.
move=> hlocal a ha; have [O [hOa [hOA hf]]] := hlocal a ha.
have [r [hr hO]] := (hf a hOa).1.
split.
- exists r; split=> // h hh; exact: hOA _ (hO h hh).
- move=> e he; have [d [hd hb]] := (hf a hOa).2 e he.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  move=> h _; rewrite lt_min=>/andP [hhr hhd].
  exact: hb h (hO h hhr) hhd.
Qed.

(** Source for [norm_class_higher_local]:
    the recursive higher differential and continuity
    conditions of Federer 3.1.11, pp. 219–220,
    can be checked on open neighborhoods.
    Uniqueness glues the local exact differential
    fields; arbitrary values outside A have
    no mathematical role. *)
Theorem norm_class_higher_local (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (f : X->Y) k :
  (forall a, A a -> exists O : X->Prop,
    O a /\ (forall x, O x -> A x) /\
    norm_class_higher NX NY ez ZN O f k) ->
  norm_class_higher NX NY ez ZN A f k.
Proof.
move=> hlocal.
have hf : norm_class_zero NX NY A f.
  apply: norm_class_zero_local=>a ha.
  have [O [hOa [hOA hc]]] := hlocal a ha.
  exists O; split; first exact hOa; split; [exact hOA|exact hc.1].
have hex a : exists z : Z k,
    A a -> has_norm_higher_differential NX ez ZN A f k a z.
  case: (pselect (A a))=>[ha|hna].
  - have [O [hOa [hOA [hc [D [hD hDc]]]]]] := hlocal a ha.
    have hopen x (hx : O x) := (hc x hx).1.
    exists (D a)=>_.
    exact: (@norm_higher_differential_open_restriction R X Y NX NY
      hNX hNY Z ez ZN hZ k A O f hOA hopen a hOa (D a)).2 (hD a hOa).
  - exists 0=>ha; exfalso; exact: hna ha.
have [D hD] := choice hex.
split; first exact hf.
exists D; split; first exact hD.
apply: norm_class_zero_local=>a ha.
have [O [hOa [hOA [hc [E [hE hEc]]]]]] := hlocal a ha.
have hopen x (hx : O x) := (hc x hx).1.
have heq x (hx : O x) : D x=E x.
  have hdO := (@norm_higher_differential_open_restriction R X Y NX NY
    hNX hNY Z ez ZN hZ k A O f hOA hopen x hx (D x)).1 (hD x (hOA x hx)).
  have hh := norm_higher_differential_unique hNX hNY hZ hdO (hE x hx). exact hh.
exists O; split; first exact hOa; split; first exact hOA.
move=>x hx; split; first exact: hopen x hx.
move=>e he; have [d [hd hb]] := (hEc x hx).2 e he.
exists d; split=> // v hv hs; rewrite (heq _ hv) (heq _ hx); exact: hb v hv hs.
Qed.
