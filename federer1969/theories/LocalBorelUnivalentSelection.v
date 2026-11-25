(** Federer (1969), 3.2.46, p. 282: globalise
    the local univalent Borel selections of 3.2.4,
    p. 244. Countably many local images are selected
    first; the earlier exact Borel selection retains one
    original source point per image. Only the image
    deficit is discarded, never all duplicate source fibres. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  CountableUnivalentSelection BorelFunctionUP TopologicalBorel
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [local_borel_univalent_selection]: countable
    localisation of the selection argument of 3.2.4,
    p. 244, supporting 3.2.46, p. 282. Local
    Borel subsets, univalence, Borel images and actual
    null image deficits are required and proved separately
    in the geometric application. No global selection
    property is assumed. *)
Theorem local_borel_univalent_selection (R : realType) (X Y : topologicalType)
    (f : X -> Y) (beta : set Y -> \bar R) (S P : set X) (U : nat -> set X) :
  is_measure beta -> is_borel_function f -> is_countable_open_base U ->
  (forall x, exists V : set X, open V /\ V x /\ exists W : set X,
    borel_set W /\ W `<=` S `&` P /\
    (forall a b, W a -> W b -> f a=f b -> a=b) /\
    borel_set (f @` W) /\ beta ((f @` (S `&` V)) `\` (f @` W))=0) ->
  exists W : set X, borel_set W /\ W `<=` S `&` P /\
    (forall a b, W a -> W b -> f a=f b -> a=b) /\
    borel_set (f @` W) /\ beta ((f @` S) `\` (f @` W))=0.
Proof.
move=> hBeta hF hBase hLocal.
pose L V W := borel_set W /\ W `<=` S `&` P /\
  (forall a b, W a -> W b -> f a=f b -> a=b) /\
  borel_set (f @` W) /\ beta ((f @` (S `&` V)) `\` (f @` W))=0.
pose C := [set V : set X | open V /\ exists W, L V W].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx [W hW]]]] := hLocal x.
  exists V; last exact hx; split; first exact hV; by exists W.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hWitness V : exists W, G V -> L V W.
  case: (pselect (G V))=> hV.
  - have [W hW] := (hGC V hV).2; exists W=> _; exact hW.
  - exists set0=> hIn; exact: False_ind _ (hV hIn).
have [W hW] := choice hWitness.
pose H := W @` G.
have hHCount : countable H := sub_countable (card_image_le _ _) hCount.
have hHBorel D (hD : H D) : borel_set D.
  have [V hV <-] := hD; exact: (hW V hV).1.
have hHInj D (hD : H D) : forall a b, D a -> D b -> f a=f b -> a=b.
  have [V hV <-] := hD; exact: (hW V hV).2.2.1.
have hHImage D (hD : H D) : borel_set (f @` D).
  have [V hV <-] := hD; exact: (hW V hV).2.2.2.1.
have [D [hD [hDSub [hDInj hImage]]]] :=
  borel_univalent_countable_selection hF hHCount hHBorel hHInj hHImage.
have hDImage : borel_set (f @` D).
  have hUnion : f @` D=\bigcup_(E in H) (f @` E).
    rewrite hImage; apply/seteqP; split=> y.
    - move=> [x [E hE hxE] hxy]; exists E; first exact hE; by exists x.
    - move=> [E hE [x hxE hxy]]; exists x; last exact hxy.
      by exists E.
  rewrite hUnion; apply: borel_set_countable_union hHCount hHImage.
exists D; split; first exact hD; split.
- move=> x hx; have [E hE hxE] := hDSub x hx.
  have [V hV hEq] := hE; rewrite -hEq in hxE.
  exact: (hW V hV).2.1 x hxE.
split; first exact hDInj; split; first exact hDImage.
pose N V := (f @` (S `&` V)) `\` (f @` W V).
have hNull V (hV : G V) : beta (N V)=0 := (hW V hV).2.2.2.2.
have hDeficitCover : ((f @` S) `\` (f @` D)) `<=` \bigcup_(V in G) N V.
  move=> y [[x hx hxy] hNot].
  have [V hV hxV] := hGCover x Logic.I.
  exists V; first exact hV; split.
  - exists x; last exact hxy; by split.
  - move=> [z hz hzy]; apply: hNot; rewrite hImage.
    exists z; last exact hzy.
    exists (W V); last exact hz; by exists V.
have hBound := measure_indexed_cover hBeta hCount hDeficitCover.
rewrite (nonnegative_sum_zero hNull) in hBound.
by apply/eqP; rewrite eq_le hBound (measure_nonnegative hBeta).
Qed.
