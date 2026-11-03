(** Federer (1969), 3.2.41, printed p. 278, last proof sentence:
    A*+B* is contained in (A+B)*. This supporting abstract argument
    isolates only monotonicity, idempotence and translation of the
    hull operation. These independent laws are proved separately
    for the actual Euclidean density-one hull before use. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [idempotent_translation_hull_vector_sum]: supporting
    last inclusion of Federer 3.2.41, p. 278. The proof takes one
    original point at a time, then takes the second hull. It does
    not infer intersection of two arbitrary nonmeasurable sets
    merely from both having full outer density. *)
Theorem idempotent_translation_hull_vector_sum (V:zmodType)
    (H:set V->set V) (A B:set V):
  (forall C D,C `<=` D ->H C `<=` H D) ->
  (forall C,H (H C)=H C) ->
  (forall (a:V) C,H [set a+x |x in C]=[set a+x |x in H C]) ->
  vector_set_sum (H A) (H B) `<=` H (vector_set_sum A B).
Proof.
move=> hMono hIdempotent hTranslate z /vector_set_sum_membership
  [a [b [ha [hb ->]]]].
pose C:=vector_set_sum A B.
have hAB:[set a+x |x in B] `<=` H C.
  move=> y [x hx <-].
  have hSub:[set x+t |t in A] `<=` C.
    move=> u [t ht <-]; rewrite addrC; exact:vector_set_sum_contains ht hx.
  have hHull:=hMono _ _ hSub.
  rewrite hTranslate in hHull.
  rewrite addrC; apply:hHull; by exists a.
have hHull:=hMono _ _ hAB.
rewrite hTranslate hIdempotent in hHull.
apply:hHull; by exists b.
Qed.
