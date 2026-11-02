(** General-topology support for Federer (1969), 2.6.6, pp. 120–121, density
    of finite-coordinate or inverse-limit pullbacks. Kelley, General
    Topology, Dover 2017 reprint of 1955, Chapter 7 Problem R(a)(ii)–(iii),
    pp. 244–245, proves density by finite pointwise maxima and minima. These
    elementary lattice operations are proved here rather than imported as an
    approximation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_maximum_list]: supporting finite maximum
    in the density argument of Federer 2.6.6, pp. 120–121;
    Kelley 7.R(a)(ii)–(iii), pp. 244–245. The anchor handles an
    empty list without an infinite value. *)
Definition function_maximum_list (R : realType) (X : Type) (a : X -> R) (s : seq (X -> R)) :=
  fun x=>foldr (fun f t=>Order.max (f x) t) (a x) s.

(** Source for [function_minimum_list]: supporting finite minimum
    in the same density argument, Kelley 7.R(a)(iii), p. 244,
    and Federer 2.6.6, pp. 120–121. *)
Definition function_minimum_list (R : realType) (X : Type) (a : X -> R) (s : seq (X -> R)) :=
  fun x=>foldr (fun f t=>Order.min (f x) t) (a x) s.

(** Source for [function_maximum_list_membership]: finite maxima
    remain in the lattice used for density in Federer 2.6.6,
    pp. 120–121; Kelley 7.R(a)(ii), p. 244. *)
Lemma function_maximum_list_membership (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (a : X -> R) (s : seq (X -> R)) :
  L a -> (forall f, f \in s -> L f) -> L (function_maximum_list a s).
Proof.
move=> ha; elim: s=> [|f s ih] hs; first exact: ha.
apply: (@function_lattice_maximum R X L hL f (function_maximum_list a s)); first exact: hs f (mem_head _ _).
apply: ih=> g hg; apply: hs; by rewrite in_cons hg orbT.
Qed.

(** Source for [function_minimum_list_membership]: finite minima
    remain in the lattice used for density in Federer 2.6.6,
    pp. 120–121; Kelley 7.R(a)(ii), p. 244. *)
Lemma function_minimum_list_membership (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (a : X -> R) (s : seq (X -> R)) :
  L a -> (forall f, f \in s -> L f) -> L (function_minimum_list a s).
Proof.
move=> ha; elim: s=> [|f s ih] hs; first exact: ha.
apply: (@function_lattice_minimum R X L hL f (function_minimum_list a s)); first exact: hs f (mem_head _ _).
apply: ih=> g hg; apply: hs; by rewrite in_cons hg orbT.
Qed.

(** Source for [function_maximum_list_member_bound]: every term
    is below the finite maximum, supporting Kelley 7.R(a)(iii),
    pp. 244–245, in Federer 2.6.6, pp. 120–121. *)
Lemma function_maximum_list_member_bound (R : realType) (X : Type)
    (a : X -> R) (s : seq (X -> R)) (f : X -> R) x :
  f \in s -> f x<=function_maximum_list a s x.
Proof.
elim: s=> [|g s ih]; first by rewrite in_nil.
rewrite in_cons=> /orP[/eqP ->|hf].
- by rewrite /function_maximum_list /= le_max lexx.
- apply: le_trans (ih hf) _; by rewrite /function_maximum_list /= le_max lexx orbT.
Qed.

(** Source for [function_minimum_list_member_bound]: the finite
    minimum is below each term, supporting the second compact-cover
    step of Kelley 7.R(a), pp. 244–245, for Federer 2.6.6,
    pp. 120–121. *)
Lemma function_minimum_list_member_bound (R : realType) (X : Type)
    (a : X -> R) (s : seq (X -> R)) (f : X -> R) x :
  f \in s -> function_minimum_list a s x<=f x.
Proof.
elim: s=> [|g s ih]; first by rewrite in_nil.
rewrite in_cons=> /orP[/eqP ->|hf].
- by rewrite /function_minimum_list /= ge_min lexx.
- apply: le_trans _ (ih hf); by rewrite /function_minimum_list /= ge_min lexx orbT.
Qed.

(** Source for [function_maximum_list_common_value]: equal values
    at the interpolation point are preserved by finite maxima,
    Kelley 7.R(a)(iii), p. 244, supporting Federer 2.6.6,
    pp. 120–121. *)
Lemma function_maximum_list_common_value (R : realType) (X : Type)
    (a : X -> R) (s : seq (X -> R)) x c :
  a x=c -> (forall f, f \in s -> f x=c) -> function_maximum_list a s x=c.
Proof.
move=> ha; elim: s=> [|f s ih] hs; first exact: ha.
change (Order.max (f x) (function_maximum_list a s x)=c).
rewrite (hs f (mem_head _ _)) ih ?maxxx // => g hg; apply: hs; by rewrite in_cons hg orbT.
Qed.

(** Source for [function_minimum_list_strict_lower]: a common
    strict lower bound is preserved by a finite minimum, in the
    compact-cover proof of Kelley 7.R(a), pp. 244–245,
    supporting Federer 2.6.6, pp. 120–121. *)
Lemma function_minimum_list_strict_lower (R : realType) (X : Type)
    (a : X -> R) (s : seq (X -> R)) x c :
  c<a x -> (forall f, f \in s -> c<f x) -> c<function_minimum_list a s x.
Proof.
move=> ha; elim: s=> [|f s ih] hs; first exact: ha.
change (is_true (c<Order.min (f x) (function_minimum_list a s x))).
rewrite lt_min (hs f (mem_head _ _)) /=; apply: ih=> g hg; apply: hs; by rewrite in_cons hg orbT.
Qed.
