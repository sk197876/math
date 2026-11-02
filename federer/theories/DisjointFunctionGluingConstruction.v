(** Private existence construction for Federer (1969), 2.5.10, p. 101, first
    paragraph. Pairwise disjointness makes local values unambiguous; choice
    gives a total function, zero elsewhere. Source context and abstract
    convention: DisjointFunctionGluingUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import DisjointFunctionGluingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [disjoint_function_gluing_exists]: existence of the sum of
    disjointly supported densities in Federer 2.5.10, p. 101 *)
Lemma disjoint_function_gluing_exists (R : realType) (X J : Type)
    (D : set J) (B : J -> set X) (f : J -> X -> R) :
  (forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) ->
  exists g : X -> R, is_disjoint_function_gluing D B f g.
Proof.
move=> hd.
have hp : forall x, exists y : R,
    (forall j, D j -> B j x -> y=f j x) /\
    (~ (\bigcup_(j in D) B j) x -> y=0).
  move=> x; case: (pselect ((\bigcup_(j in D) B j) x))=> [[i hi hxi]|hn].
  - exists (f i x); split.
    + move=> j hj hxj; have he : i=j.
        apply: contrapT=> hn.
        have hx : (B i `&` B j) x by split.
        by rewrite (hd i j hi hj hn) in hx.
      by rewrite he.
    + move=> hn; exfalso; apply: hn; by exists i.
  - exists 0; split=> // j hj hxj; exfalso; apply: hn; by exists j.
exists (fun x => projT1 (cid (hp x))); split.
- move=> j x hj hx; exact: (projT2 (cid (hp x))).1 j hj hx.
- move=> x hx; exact: (projT2 (cid (hp x))).2 hx.
Qed.
