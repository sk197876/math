(** Federer (1969), 2.3.6, p. 77: paste the closed continuity pieces and
    assign one value on their null complement. A target point is required
    for a total representative when the source is nonempty. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionExtensionSealed PartialContinuityUP ContinuousClosedPieceBorel
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelFunctionUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_version_from_closed_cover]: supporting
    corollary proof for Federer 2.3.6, p. 77. Closed
    continuity pieces need only cover almost all the source;
    no disjointness assumption is needed since their values agree. *)
Theorem borel_version_from_closed_cover (R : realType) (X Y : topologicalType)
    (J : countType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (y0 : Y) (C : J -> set X) :
  (forall j, closed (C j)) ->
  (forall j, partial_function_continuous_on (C j) f) ->
  measure_almost_everywhere mu (\bigcup_j C j) ->
  exists h : X -> Y, is_borel_function h /\ measure_almost_equal mu f (partial_function_total h).
Proof.
move=> hC hcont hnull.
pose S := \bigcup_j C j.
pose g := @PartialFunctionExtension.value X Y f y0.
have hg := @PartialFunctionExtension.laws X Y f y0.
pose h x := if pselect (S x) then g x else y0.
have hvalue x : S x -> partial_function_graph f x (h x).
  move=> [j _ hx]; have hs : S x by exists j.
  have [y hy] := @partial_continuity_domain X Y (C j) f (hcont j) x hx.
  rewrite /h; case: (pselect (S x))=> hs'; last contradiction.
  by rewrite /g (hg x y hy).
exists h; split.
- move=> U hU.
  have hpieces : borel_set (\bigcup_j (C j `&` partial_function_preimage f U)).
    apply: borel_set_countable_union; first exact: countableP.
    move=> j _; exact (@continuous_closed_piece_borel_preimage X Y (C j) f (hC j) (hcont j) U hU).
  have hS : borel_set S.
    apply: borel_set_countable_union; first exact: countableP.
    move=> j _; exact: closed_borel_set (hC j).
  have heq : h @^-1` U = (\bigcup_j (C j `&` partial_function_preimage f U)) `|`
      (if pselect (U y0) then ~` S else set0).
    apply/seteqP; split=> x.
    + move=> hu; case: (pselect (S x))=> hs.
      * left; have [j _ hx] := hs; exists j; first exact Logic.I.
        split=> //; exists (h x); split=> //; exact: hvalue hs.
      * right; have hy : U y0.
          move: hu; rewrite /preimage /h /=; case: (pselect (S x))=> hxS.
          - exfalso; exact: hs hxS.
          - by [].
        case: (pselect (U y0))=> hy0 //; exfalso; exact: hy0 hy.
    + move=> [[j _ [hx [y [hy huy]]]]|hx].
      * have hs : S x by exists j.
        have he := @partial_function_single_valued X Y f x (h x) y (hvalue x hs) hy.
        by rewrite /preimage /= he.
      * move: hx; case: (pselect (U y0))=> hu; last by move=> [].
        move=> hs; rewrite /preimage /h /=.
        case: (pselect (S x))=> hxS.
        - exfalso; exact: hs hxS.
        - exact hu.
  rewrite heq; apply: (borel_family_binary_union (borel_sets_family X) hpieces).
  case: (pselect (U y0))=> hcase; first exact: borel_set_complement hS.
  exact: open_borel_set open0.
- apply: (@measure_almost_everywhere_mono R X mu hm S _ _ hnull).
  move=> x hx; exists (h x); split; first exact: hvalue hx.
  by [].
Qed.
