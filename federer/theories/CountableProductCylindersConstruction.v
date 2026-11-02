(** Federer (1969), 2.3.2(5), p. 73: private countable finite-cylinder
    refinement. We prove the general topology argument from coordinate
    neighborhood convergence and the finite-intersection filter. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CountableProductCylindersUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [countable_product_cylinders_countable]: supporting
    countability of basic coordinate cylinders for Federer 2.3.2(5), p. 73 *)
Lemma countable_product_cylinders_countable (I : choiceType) (Y : I -> topologicalType)
    (U : forall i, nat -> set (Y i)) :
  countable (@setT I) -> countable (product_coordinate_cylinders U).
Proof.
move=> hi; apply: bigcup_countable hi _=> i _.
apply: sub_countable (card_image_le _ _) _; exact: countableP.
Qed.

(** Source for [countable_product_cylinder_refinement_exists]:
    supporting general-topology existence argument for Federer
    2.3.2(5), p. 73. Every open set is refined by the
    countable family of finite basic-cylinder intersections. The
    proof includes empty products and empty finite intersections. *)
Theorem countable_product_cylinder_refinement_exists (I : choiceType)
    (Y : I -> topologicalType) (U : forall i, nat -> set (Y i)) :
  countable (@setT I) -> (forall i, is_countable_open_base (U i)) ->
  exists B, is_countable_product_cylinder_refinement U B.
Proof.
move=> hi hU; pose C := product_coordinate_cylinders U.
pose B := finI_from C id.
exists B; constructor.
- apply: finI_from_countable; exact: countable_product_cylinders_countable hi.
- by move=> W hW.
- move=> V ho x hx.
  pose F := filter_from [set W | B W /\ W x] id.
  have hF : Filter F.
    apply: filter_from_filter.
    + exists setT; split=> //.
      exists fset0; first by move=> W; rewrite inE.
      by rewrite set_fset0 bigcap_set0.
    + move=> A D [hA hxA] [hD hxD]; exists (A `&` D); last by move=> y hy.
      split; last by split.
      exact: finI_fromI hA hD.
  have hc : F --> (x : prod_topology Y).
    apply/cvg_sup=> i V'; rewrite (@nbhsE (initial_topology (fun y : prod_topology Y => y i))).
    move=> [W [[O hO <-] hxi] hWV].
    have [n [hn hns]] := @countable_base_refines (Y i) (U i) (hU i) O hO (x i) hxi.
    exists [set y : prod_topology Y | U i n (y i)].
    + split=> //; apply: finI_from1.
      exists i; first exact Logic.I.
      by exists n.
    + move=> y hy; apply: hWV; exact: hns _ hy.
  have hnb : nbhs x V by rewrite openE in ho; exact: ho x hx.
  have [W [hW hxW] hWV] := hc V hnb.
  by exists W.
Qed.
