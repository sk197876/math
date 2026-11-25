(** Federer (1969), 2.1.6, pp. 58-59: supporting null-cover consequence of
    the disjoint-family characterisation. A choice of one covering member at
    each point gives a disjoint refinement. All subsets of the union are
    assumed measurable here. This stronger measurability hypothesis permits
    arbitrary covers, and will replace the cardinal-product estimate in the
    successor argument by a null-set argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureDisjointFamily
  UlamCardinalUP UlamNullFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_null_cover]: Federer 2.1.6, pp. 58-59,
    supporting consequence of the second definition. A family of null
    sets indexed by an Ulam set has null union if the union has finite
    measure and all of its subsets are measurable. Unlike the printed
    defining property, disjointness is not needed under this stronger
    measurability hypothesis. *)
Theorem ulam_null_cover (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (D : set J) (F : J -> set I) :
  is_ulam_set R D -> mu (\bigcup_(j in D) F j) < +oo ->
  (forall A, A `<=` \bigcup_(j in D) F j -> measure_measurable mu A) ->
  (forall j, D j -> mu (F j) = 0) -> mu (\bigcup_(j in D) F j) = 0.
Proof.
move=> hu hf ha hz; pose X := \bigcup_(j in D) F j.
have hc x : exists k : option J,
  X x -> exists j, D j /\ F j x /\ k = Some j.
  case: (pselect (X x))=> [[j hj hx]|hn].
  - exists (Some j)=> _; exists j; by split=> //; split.
  - exists None=> hx; exfalso; exact: hn hx.
pose p x := projT1 (cid (hc x)).
have hp x : X x -> exists j, D j /\ F j x /\ p x = Some j.
  exact: projT2 (cid (hc x)).
pose G j : set I := [set x | X x /\ p x = Some j].
have hG j : D j -> G j `<=` F j.
  move=> hj x [hx he]; have [k [hk [hkx hek]]] := hp x hx.
  have hkj : k = j by move: hek; rewrite he; case.
  by rewrite -hkj.
have he : (\bigcup_(j in D) G j) = X.
  apply/seteqP; split=> [x [j hj [hx _]]|x hx] //.
  have [j [hj [_ hjp]]] := hp x hx; exists j=> //; by split.
have hd j k : D j -> D k -> j <> k -> G j `&` G k = set0.
  move=> hj hk hn; apply/seteqP; split=> [x [[hx hjp] [_ hkp]]|x []].
  exfalso; apply: hn; by move: hjp; rewrite hkp; case.
change (mu X = 0); rewrite -he; apply: (@ulam_set_null_families R J D hu I J mu D G hm (card_lexx D) hd).
- by rewrite he.
- move=> A; apply: ha=> x [j [hj _] [hx _]]; exact hx.
- move=> j hj; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have h := @measure_mono R I mu hm (G j) (F j) (hG j hj).
  by rewrite (hz j hj) in h.
Qed.
