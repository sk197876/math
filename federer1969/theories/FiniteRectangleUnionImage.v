(** Federer (1969), 2.6.4, pp. 118–119: the finite union step of the
    characteristic-function density argument. Finite unions of rectangles
    with finite measurable factors have characteristic functions in the
    tensor image exactly, by inclusion-exclusion and intersections of
    rectangles. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicUnionArithmetic
  SetSequenceDisjointification SummableTensorImage SummableRectangleIndicators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Unions.
Variable R : realType.
Variables X Y : choiceType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Variables (ha : is_measure alpha) (hb : is_measure beta).

(** Source for [finite_rectangle_union_characteristic_image]:
    exact finite-union membership underlying the P1 step in
    Federer 2.6.4, pp. 118–119. The empty union
    is included, and the proof adds no quotient convention. *)
Theorem finite_rectangle_union_characteristic_image (A : nat -> set X) (B : nat -> set Y)
    (n : nat) (s : (X*Y) -> R) :
  (forall k, measure_measurable alpha (A k) /\ (alpha (A k) < +oo)%E /\
    measure_measurable beta (B k) /\ (beta (B k) < +oo)%E) ->
  is_characteristic_function (set_sequence_prefix (fun k => A k `*` B k) n) s ->
  separated_summable_image ha hb s.
Proof.
elim: n A B s=> [|n IH] A B s hAB hs.
- have he : s=(fun _ => 0).
    apply: funext=> p; apply: (@characteristic_off_set R (X*Y)%type
      (set_sequence_prefix (fun k => A k `*` B k) 0) s hs p).
    by rewrite set_sequence_prefix_zero.
  rewrite he; exact: separated_summable_image_zero.
- pose P := set_sequence_prefix (fun k => A k `*` B k) n.
  pose Q := A n `*` B n.
  pose C k := A k `&` A n.
  pose D k := B k `&` B n.
  pose E := set_sequence_prefix (fun k => C k `*` D k) n.
  pose a := @CharacteristicFunction.value R (X*Y)%type P.
  pose b := @CharacteristicFunction.value R (X*Y)%type Q.
  pose c := @CharacteristicFunction.value R (X*Y)%type E.
  have ha' : is_characteristic_function P a := @CharacteristicFunction.laws R (X*Y)%type P.
  have hb' : is_characteristic_function Q b := @CharacteristicFunction.laws R (X*Y)%type Q.
  have hc' : is_characteristic_function E c := @CharacteristicFunction.laws R (X*Y)%type E.
  have hPQ : P `&` Q=E.
    apply/seteqP; split.
    + move=> [x y] [[k hk [hx hy]] [hxn hyn]]; exists k=> //; by split; split.
    + move=> [x y] [k hk [[hx hxn] [hy hyn]]]; split; last by split.
      exists k=> //; by split.
  have hc : is_characteristic_function (P `&` Q) c by rewrite hPQ.
  have hu := characteristic_union_difference ha' hb' hc.
  rewrite set_sequence_prefix_succ in hs.
  have he : s=(fun p => a p+b p-c p).
    apply: funext=> p; exact (@characteristic_function_unique R (X*Y)%type (P `|` Q)
      s (fun p => a p+b p-c p) hs hu p).
  rewrite he; apply: separated_summable_image_subtract.
  + apply: separated_summable_image_add.
    * exact: IH A B a hAB ha'.
    * exact (@finite_rectangle_characteristic_image R X Y alpha beta ha hb (A n) (B n) b
        (hAB n).1 (hAB n).2.1 (hAB n).2.2.1 (hAB n).2.2.2 hb').
  + apply: (IH C D c)=> // k; split.
    * exact (@measure_measurable_intersection R X alpha ha (A k) (A n) (hAB k).1 (hAB n).1).
    * split.
      -- apply: le_lt_trans (@measure_mono R X alpha ha (C k) (A k) _) (hAB k).2.1.
         by move=> x [hx _].
      -- split.
         ++ exact (@measure_measurable_intersection R Y beta hb (B k) (B n) (hAB k).2.2.1 (hAB n).2.2.1).
         ++ apply: le_lt_trans (@measure_mono R Y beta hb (D k) (B k) _) (hAB k).2.2.2.
            by move=> y [hy _].
Qed.
End Unions.
