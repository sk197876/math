(** Federer (1969), 2.2.14, p. 70: Borel sets are exactly the sets with
    Borel characteristic functions. The proof uses the abstract one/zero
    laws and Borel preimage closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground TopologicalBorel BorelFamilyBasic
  BorelFunctionUP BorelFunctionBasic CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_preimage_one]: supporting recovery
    of the set from its characteristic function in Federer
    2.2.14, p. 70. The scalar values zero and one
    are distinct in the real field. *)
Lemma characteristic_preimage_one (R : realType) (X : Type) (A : set X)
    (f : X -> R) : is_characteristic_function A f -> f @^-1` [set 1] = A.
Proof.
move=> hf; apply/seteqP; split.
- move=> x hx; apply: contrapT=> hn.
  have he : f x = 1 := hx.
  rewrite (characteristic_off_set hf hn) in he.
  by move/eqP: he; rewrite eq_sym oner_eq0.
- move=> x hx; change (f x = 1).
  exact: (@characteristic_on_set R X A f hf x hx).
Qed.

(** Source for [characteristic_function_borel_iff]: direct
    characteristic-function equivalence in Federer 2.2.14, p. 70.
    The forward implication uses only the four possible preimages
    determined by whether a target set contains zero and one;
    the reverse takes the preimage of the closed singleton one. *)
Theorem characteristic_function_borel_iff (R : realType) (X : topologicalType)
    (A : set X) (f : X -> real_line_metric R) :
  is_characteristic_function A f ->
  (borel_set A <-> is_borel_function f).
Proof.
move=> hf; split.
- move=> hA U hU.
  have hpre : f @^-1` U = [set x | A x /\ U 1] `|` [set x | ~ A x /\ U 0].
    apply/seteqP; split.
    + move=> x hx; change (U (f x)) in hx; case: (pselect (A x))=> ha.
      * left; split=> //; by move: hx; rewrite (characteristic_on_set hf ha).
      * right; split=> //; by move: hx; rewrite (characteristic_off_set hf ha).
    + move=> x [[ha h1]|[ha h0]]; rewrite /preimage /=.
      * by rewrite (characteristic_on_set hf ha).
      * by rewrite (characteristic_off_set hf ha).
  rewrite hpre; apply: (borel_family_binary_union (borel_sets_family X)).
  + case: (pselect (U 1))=> h1.
    * have -> : [set x | A x /\ U 1] = A by apply/seteqP; split=> [x [hx _]|x hx] //; by split.
      exact hA.
    * have -> : [set x | A x /\ U 1] = set0 by apply/seteqP; split=> [x [_ hx]|x []]; exact: h1 hx.
      exact: open_borel_set open0.
  + case: (pselect (U 0))=> h0.
    * have -> : [set x | ~ A x /\ U 0] = ~` A by apply/seteqP; split=> [x [hx _]|x hx] //; by split.
      exact: borel_set_complement hA.
    * have -> : [set x | ~ A x /\ U 0] = set0 by apply/seteqP; split=> [x [_ hx]|x []]; exact: h0 hx.
      exact: open_borel_set open0.
- move=> hfb; rewrite -(characteristic_preimage_one hf).
  apply: (@borel_function_preimage X [the topologicalType of real_line_metric R] f hfb [set 1]); apply: closed_borel_set.
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [borel_iff_characteristic_borel]: public sealed
    form of the equivalence in Federer 2.2.14, p. 70.
    The proof uses only the exposed characteristic-function laws. *)
Theorem borel_iff_characteristic_borel (R : realType) (X : topologicalType) (A : set X) :
  borel_set A <-> @is_borel_function X [the topologicalType of real_line_metric R]
    (@CharacteristicFunction.value R X A).
Proof. exact: characteristic_function_borel_iff (@CharacteristicFunction.laws R X A). Qed.
