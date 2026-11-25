(** Federer (1969), 3.2.35, p. 271:
    translation preserves the exact original boundary
    in the reduction to a body containing zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import InnerProductUP InnerMetric InnerTranslationNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_translation_closure]: supporting
    the closure in the translated boundary of
    Federer 3.2.35, p. 271. Actual
    translated neighbourhoods prove both directions
    for every original set. *)
Lemma inner_translation_closure (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V) a x:
  @closure [the topologicalType of inner_metric_space hB]
    ((fun z:V=>z+a) @^-1` A) x <->
  @closure [the topologicalType of inner_metric_space hB] A (x+a).
Proof.
split=>hx U hU.
- have hPre:=(@inner_translation_neighbourhood R V B hB a x U).1 hU.
  have [y [hy hUy]]:=hx _ hPre.
  exists (y+a); by split.
- have hShift:=(@inner_translation_neighbourhood R V B hB (-a) (x+a) U).
  rewrite addrK in hShift.
  have [y [hy hUy]]:=hx _ (hShift.1 hU).
  exists (y-a); split; last exact hUy.
  change (A ((y-a)+a)); by rewrite subrK.
Qed.

(** Source for [inner_translation_boundary_image]: the
    exact original boundary after the translation
    reduction in Federer 3.2.35, p. 271.
    The actual closure equivalence and neighbourhood
    equivalence identify the image of closure minus
    interior, without an openness or regularity premise. *)
Lemma inner_translation_boundary_image (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V) a:
  let T:=[the topologicalType of inner_metric_space hB] in
  (fun x:V=>x+a) @`
    (@closure T ((fun z:V=>z+a) @^-1` A) `\`
      @interior T ((fun z:V=>z+a) @^-1` A))=
    (@closure T A `\` @interior T A).
Proof.
move=>T; apply/seteqP; split=>y.
- move=>[x [hx hOutside] <-]; split.
  + exact:(@inner_translation_closure R V B hB A a x).1 hx.
  + move=>hInterior; apply:hOutside.
    exact:(@inner_translation_neighbourhood R V B hB a x A).1 hInterior.
- move=>[hy hOutside]; exists (y-a); last exact:subrK.
  split.
  + apply:(@inner_translation_closure R V B hB A a (y-a)).2.
    by rewrite subrK.
  + move=>hInterior; apply:hOutside.
    have hh:=(@inner_translation_neighbourhood R V B hB a (y-a) A).2 hInterior.
    by rewrite subrK in hh.
Qed.
