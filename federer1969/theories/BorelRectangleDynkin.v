(** Supporting Federer (1969), 2.10.46, p. 204: a rectangle induction
    principle for Borel sets in a product of spaces with countable bases.
    Countable unions of basic rectangles generate the open sets, as in the
    product Borel argument for 2.6.5, p. 120. The auxiliary pi-lambda
    criterion is proved locally from the generated-family laws of 2.2.1, pp.
    59–60. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import DynkinFamilyUP DynkinBorelCriterion GeneratedBorel BorelFamilyUP BorelFamilyBasic
  TopologicalBorel CountableOpenBaseUP CompactTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_product_dynkin_criterion]: supporting
    rectangle induction for 2.10.46, p. 204, through
    the product Borel generation in 2.6.5, p. 120.
    No measure or completion is built into this set-theoretic
    criterion. *)
Theorem borel_product_dynkin_criterion (X Y : topologicalType)
    (U : nat -> set X) (V : nat -> set Y) (F : set (set (X*Y))) :
  is_countable_open_base U -> is_countable_open_base V -> is_dynkin_family F ->
  (forall A B, borel_set A -> borel_set B -> F (A `*` B)) ->
  forall S, borel_set S -> F S.
Proof.
move=> hU hV hF hrect.
pose P := [set S : set (X*Y) | exists A B, borel_set A /\ borel_set B /\ S=A `*` B].
have hPwithin : forall A, P A -> A `<=` setT by move=> A _; exact: subsetT.
pose G := generated_borel_family hPwithin.
have hG := generated_borel_family_specification hPwithin.
have hpi A B : P A -> P B -> P (A `&` B).
  move=> [A1 [A2 [hA1 [hA2 ->]]]] [B1 [B2 [hB1 [hB2 ->]]]].
  exists (A1 `&` B1), (A2 `&` B2); split.
  - exact: (borel_family_binary_intersection (borel_sets_family X)).
  - split; first exact: (borel_family_binary_intersection (borel_sets_family Y)).
    apply/seteqP; split=> [[x y] [[ha1 ha2] [hb1 hb2]]|[x y] [[ha1 hb1] [ha2 hb2]]]; by split; split.
have hPF : P `<=` F by move=> S [A [B [hA [hB ->]]]]; exact: hrect.
have hGF : G `<=` F := dynkin_generated_borel_inclusion hG hpi hF hPF.
have hopen O : open O -> G O.
  move=> hO; pose D := [set p : nat*nat | U p.1 `*` V p.2 `<=` O].
  have he : O=\bigcup_(p in D) (U p.1 `*` V p.2).
    apply/seteqP; split.
    - move=> [x y] hxy.
      have [A [B [hA [hB [hx [hy hAB]]]]]] := open_product_rectangle_at hO hxy.
      have [i [hi hiA]] := @countable_base_refines X U hU A hA x hx.
      have [j [hj hjB]] := @countable_base_refines Y V hV B hB y hy.
      exists (i,j); last by split.
      move=> [a b] [ha hb]; apply: hAB; split; [exact: hiA a ha|exact: hjB b hb].
    - by move=> p [ij hij hp]; exact: hij p hp.
  rewrite he; apply (@borel_family_indexed_union (X*Y)%type [the choiceType of ((nat : Type)*(nat : Type))%type]
    setT G (generated_borel_family_laws hG) D (fun p=>U p.1 `*` V p.2) (countableP D)).
  move=> [i j] _.
  apply: (generated_borel_family_contains hG); exists (U i),(V j); split.
  - exact: open_borel_set (countable_base_open hU i).
  - split=> //; exact: open_borel_set (countable_base_open hV j).
have hBG : @borel_set (X*Y)%type `<=` G := generated_borel_family_least
  (borel_sets_specification (X*Y)%type) (generated_borel_family_laws hG) hopen.
move=> S hS; exact: hGF _ (hBG S hS).
Qed.
