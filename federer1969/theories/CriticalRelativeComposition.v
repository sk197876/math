(** Federer (1969), 3.4.2(6)–(7), pp. 312–313: compose a relatively
    class-k map with an ambient class-k map taking values in its source. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormRegularity NormRegularityOperations
  NormRegularityLocal RelativeClassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_relative_class_composition]: supporting the
    map f composed with the projection retraction r in 3.4.2(6)–(7),
    pp. 312–313. The local ambient extensions defining relative class
    compose with the original r; locality proves class k on its whole
    original open domain. All three normed spaces are arbitrary. *)
Theorem critical_relative_class_composition (R:realType) (X V Y:lmodType R)
    (NX:X->R) (NV:V->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNV:is_real_norm NV) (hNY:is_real_norm NY)
    (U:X->Prop) (S:V->Prop) (r:X->V) (f:V->Y) k:
  norm_class hNX hNV U r k ->(forall x,U x ->S (r x)) ->
  norm_class_relative hNV hNY S S f k ->
  norm_class hNX hNY U (fun x=>f (r x)) k.
Proof.
move=>hr hMap hf.
apply:norm_class_local_representatives=>a ha.
have [O [g [hRaO [hg hAgree]]]]:=hf (r a) (hMap a ha).
exists (fun x=>U x /\O (r x)),(fun x=>g (r x)).
split;first by split.
split;first by move=>x [hx _].
split;first exact:(norm_class_composition hr hg).
move=>x [hx hxO];symmetry.
exact:(hAgree (r x) (hMap x hx) hxO).2.
Qed.
