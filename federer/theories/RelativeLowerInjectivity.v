(** Federer (1969), 3.2.2, p. 242: positive lower
    distance bounds imply injectivity, both for a differential
    and for the map on each small Borel piece. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relative_lower_bound_injective]: the univalence
    of f restricted to E in Federer 3.2.2, p. 242.
    A positive norm lower bound through any injective source
    map separates all pairs of points in E. *)
Lemma relative_lower_bound_injective (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (E:set X) (f:X->Y) (s:Hom X X) (c:R) :
  injective s -> 0<c ->
  (forall x y,E x -> E y -> c*NX (s (x-y))<=NY (f x-f y)) ->
  {in E &,injective f}.
Proof.
move=>hs hc hLower x y hx hy hxy.
have hxE:E x:=set_mem hx.
have hyE:E y:=set_mem hy.
have hh:=hLower x y hxE hyE; rewrite hxy subrr (real_seminorm_zero hNY.1) in hh.
have hn:=real_seminorm_nonnegative hNX.1 (s (x-y)).
have hz:NX (s (x-y))=0 by nra.
have hsz:=hNX.2 _ hz.
have hd:x-y=0 by apply:hs; rewrite linear0.
by apply/eqP; rewrite -subr_eq0 hd eqxx.
Qed.

(** Source for [linear_relative_lower_injective]: the first
    condition on Z(s,i) forces an injective differential,
    Federer 3.2.2, p. 242. The positive lower scalar
    and actual source automorphism are the only hypotheses. *)
Lemma linear_relative_lower_injective (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (s:Hom X X) (D:Hom X Y) (c:R) :
  injective s -> 0<c -> (forall v,c*NX (s v)<=NY (D v)) -> injective D.
Proof.
move=>hs hc hb x y hxy.
have h:forall a b,setT a -> setT b -> c*NX (s (a-b))<=NY (D a-D b).
  move=>a b _ _; rewrite -linearB; exact (hb (a-b)).
exact ((relative_lower_bound_injective hNX hNY hs hc h) x y (mem_set Logic.I) (mem_set Logic.I) hxy).
Qed.
