(** Federer (1969), 2.1.6(1), p. 58: a union of Ulam cardinal
    representatives indexed by an Ulam set is Ulam. For a family of initial
    ordinal representatives this union is their least upper bound, as in the
    book. The more general set-union statement below uses a null cover and
    its disjoint refinement. Kelley, General Topology, Appendix, pp. 275-276
    (2017 reprint of 1955) supplies the cardinal-comparison background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic UlamCardinalUP
  UlamNullCover CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_set_union]: Federer 2.1.6(1), p. 58,
    paraphrased: the supremum of Ulam cardinals is Ulam if its
    indexing set has Ulam cardinality. We prove the set-union form,
    which specialises to the printed union of ordinal representatives.
    Preimages of the covering sets have Ulam cardinality and hence
    are null; a disjoint refinement completes the argument. *)
Theorem ulam_set_union (R : realType) (J K : choiceType)
    (D : set J) (F : J -> set K) :
  is_ulam_set R D -> (forall j, D j -> is_ulam_set R (F j)) ->
  is_ulam_set R (\bigcup_(j in D) F j).
Proof.
move=> hD hF I mu X hm hX hf ha hz.
pose U := \bigcup_(j in D) F j.
case: (pselect (exists u, U u))=> [[d hd]|hempty]; last first.
  have he : U = set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  have hx0 : X = set0.
    have hc : X #<= U := hX; rewrite he in hc.
    exact: (elimT (@card_le0P I K X) hc).
  by rewrite hx0 (measure_empty hm).
have [f [hfun hinj]] := @cardinal_injection_with_default I K X U d hX.
pose G j : set I := [set x | X x /\ F j (f x)].
have hGX j : G j `<=` X by move=> x [hx _].
have hGc j : D j -> G j #<= F j.
  move=> hj; have [g] : $|{injfun G j >-> F j}|.
    apply/injfunPex; exists f.
    - by move=> x [hx hfx].
    - move=> x y hx hy he; apply: hinj he.
      + exact: mem_set (hGX j x (set_mem hx)).
      + exact: mem_set (hGX j y (set_mem hy)).
  exact: inj_card_le g.
have hGz j : D j -> mu (G j) = 0.
  move=> hj; apply: (hF j hj I mu (G j) hm (hGc j hj)).
  - exact: le_lt_trans (@measure_mono R I mu hm _ X (hGX j)) hf.
  - move=> A hA; apply: ha=> x hx; exact: hGX j x (hA x hx).
  - move=> x hx; exact: hz x (hGX j x hx).
have he : (\bigcup_(j in D) G j) = X.
  apply/seteqP; split=> [x [j _ [hx _]]|x hx] //.
  have [j hj hfx] := hfun x hx; exists j=> //; by split.
rewrite -he; apply: (@ulam_null_cover R I J mu hm D G hD).
- by rewrite he.
- move=> A hA; apply: ha; by rewrite -he.
- exact hGz.
Qed.
