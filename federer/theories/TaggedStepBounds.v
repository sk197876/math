(** Federer (1969), 2.9.24, p. 169: the step approximations take values of f
    on the partition and vanish outside it. Their boundedness follows from
    boundedness of the BV image. The local Federer erratum has no entry for
    this step. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import CurveVariationUP TaggedStepFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [tagged_step_function_value_bound]: supporting uniform bound
    on the step functions in Federer 2.9.24, p. 169 A nonnegative bound for
    all tag values also bounds the zero exterior value. *)
Lemma tagged_step_function_value_bound (R : realType) (f : R -> R)
    (w : seq R) (M : R) : 0<=M ->
  (forall t, t \in w -> `|f t|<=M) ->
  forall x : R, `|tagged_step_function f w x|<=M.
Proof.
move=> hM; have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|a [|r [|b rest]]] hs htags x.
- by rewrite (@tagged_step_function_short R f [::] _ x) // normr0.
- by rewrite (@tagged_step_function_short R f [:: a] _ x) // normr0.
- by rewrite (@tagged_step_function_short R f [:: a;r] _ x) // normr0.
- rewrite tagged_step_function_cons; case: ifP=> hx.
  + apply: htags; by rewrite !in_cons eqxx orbT.
  + have hsize : (size (b::rest)<n)%N by move: hs; rewrite /= !ltnS; exact: ltnW.
    apply: (ih (b::rest) hsize)=> t ht.
    apply: htags; rewrite in_cons; apply/orP; right.
    rewrite in_cons; apply/orP; right; exact: ht.
Qed.

(** Source for [tagged_step_function_outside]: supporting zero
    extension outside the cells of the approximations in Federer
    2.9.24, p. 169. The left endpoint is excluded and
    the right endpoint included, as in the printed f_n. *)
Lemma tagged_step_function_outside (R : realType) (f : R -> R) (w : seq R) :
  sorted <=%O w -> forall x : R,
    x<=head 0 w \/ last 0 w<x -> tagged_step_function f w x=0.
Proof.
have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|a [|r [|b rest]]] hsize hs x hout.
- exact: (@tagged_step_function_short R f [::] _ x).
- exact: (@tagged_step_function_short R f [:: a] _ x).
- exact: (@tagged_step_function_short R f [:: a;r] _ x).
- have /andP[har /andP[hrb htail]] := hs.
  have hab : a<=b := le_trans har hrb.
  have hbl : b<=last 0 (b::rest).
    exact (@sorted_le_last R (b::rest) 0 b htail (mem_head b rest)).
  rewrite tagged_step_function_cons; case: ifP=> hx.
  + have /andP[hax hxb] := hx.
    case: hout=> ho.
    * change (is_true (x<=a)) in ho; lra.
    * change (is_true (last 0 (b::rest)<x)) in ho; lra.
  + have hsmall : (size (b::rest)<n)%N by move: hsize; rewrite /= !ltnS; exact: ltnW.
    apply: (ih (b::rest) hsmall htail).
    case: hout=> ho.
    * left; change (is_true (x<=a)) in ho; by rewrite /=; lra.
    * right; exact: ho.
Qed.
