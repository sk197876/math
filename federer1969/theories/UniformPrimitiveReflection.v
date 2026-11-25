(** Elementary reflected primitive supporting Federer (1969), 2.10.36, p.
    198, the last volume estimate for the symmetric two-apex convex hull.
    Its negative-height power integral is obtained by reflection of the
    positive-height primitive used in 2.7.16, p. 136. Derive the reflection
    from the project's finite-increment primitive specification; no external
    calculus theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import UniformPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_primitive_reflection]: supporting
    reflection of the scalar power integral
    implicit in the last estimate of
    2.10.36, p. 198. Reversing
    both interval endpoints preserves the
    finite-increment error bound exactly. *)
Theorem uniform_primitive_reflection (R : realType) (f F : R -> R) (a b : R) :
  is_uniform_primitive_on f F a b ->
  is_uniform_primitive_on (fun t=>f (-t)) (fun t=> -F (-t)) (-b) (-a).
Proof.
move=> hp e he; have [d [hd hh]] := hp e he.
exists d; split=> // s u t hs hsu hut ht hgap.
have h1 : a<= -t by lra.
have h2 : -t<= -u by lra.
have h3 : -u<= -s by lra.
have h4 : -s<=b by lra.
have hdiff : -s-(-t)=t-s by ring.
have hsmall : -s-(-t)<d by rewrite hdiff.
have hb := hh (-t) (-u) (-s) h1 h2 h3 h4 hsmall.
rewrite hdiff in hb.
have heq : -F (-t)-(-F (-s))-f (-u)*(t-s)=F (-s)-F (-t)-f (-u)*(t-s) by ring.
by rewrite heq.
Qed.
