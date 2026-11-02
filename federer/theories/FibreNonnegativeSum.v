(** Federer (1969), 2.5.10, p. 101: summing function values over p^{-1}{t}.
    For nonnegative functions the arbitrary sum is always defined by
    2.1.1(3), p. 52. Expansion into characteristic functions uses
    2.1.1(6),(10), pp. 52–53. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NonnegativeSumScale
  NonnegativeSumProduct CountingMeasure CharacteristicFunctionUP MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fibre_nonnegative_sum]: the nonnegative
    fibre sum in Federer 2.5.10, p. 101,
    using the sealed arbitrary summation of 2.1.1(3),
    p. 52. The indexing fibre may be uncountable. *)
Definition fibre_nonnegative_sum (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (f : X -> \bar R) y :=
  nonnegative_sum [set x | p x=y] f.

(** Source for [fibre_characteristic_sum]: the fibre sum
    of a characteristic function is its multiplicity,
    Federer 2.10.9–10, pp. 175–176, supporting
    the formula of 2.5.10, p. 101. *)
Lemma fibre_characteristic_sum (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> forall y,
  fibre_nonnegative_sum p (fun x => (s x)%:E) y=@mapping_multiplicity R X Y p A y.
Proof.
move=> hs y; rewrite /fibre_nonnegative_sum /mapping_multiplicity counting_measure_sum.
have he : mapping_fibre p A y=[set x | p x=y] `&` A.
  by apply/seteqP; split=> x [h1 h2]; split.
rewrite he -nonnegative_sum_restrict; apply: nonnegative_sum_ext=> x hx.
case: (pselect (A x))=> hAx.
- by rewrite (mem_set hAx) (characteristic_on_set hs hAx).
- have hn : x \notin A by apply/negP=> /set_mem hh; exact: hAx.
  by rewrite (negbTE hn) (characteristic_off_set hs hAx).
Qed.

(** Source for [fibre_characteristic_expansion_sum]:
    supporting interchange for the characteristic expansion
    of the fibre sum in Federer 2.5.10, p. 101,
    by 2.1.1(6),(10), pp. 52–53. It includes
    infinite multiplicities and infinite sums. *)
Lemma fibre_characteristic_expansion_sum (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (f : X -> \bar R) (r : nat -> R)
    (E : nat -> set X) (s : nat -> X -> R) :
  (forall n, (0<=r n)%R) -> (forall n, is_characteristic_function (E n) (s n)) ->
  (forall x, nonnegative_sum setT (fun n => (r n*s n x)%R%:E)=f x) -> forall y,
  fibre_nonnegative_sum p f y=nonnegative_sum setT
    (fun n => (r n)%:E * @mapping_multiplicity R X Y p (E n) y).
Proof.
move=> hr hs hf y.
have hp n x : 0<=(r n*s n x)%R%:E.
  rewrite lee_fin; apply: mulr_ge0 (hr n) _.
  case: (pselect (E n x))=> h; [rewrite (characteristic_on_set (hs n) h)|rewrite (characteristic_off_set (hs n) h)]; exact: ler01 || exact: lexx.
have he : fibre_nonnegative_sum p f y=nonnegative_sum [set x | p x=y]
    (fun x => nonnegative_sum setT (fun n => (r n*s n x)%R%:E)).
  apply: nonnegative_sum_ext=> x hx; symmetry; exact: hf.
rewrite he -(@nonnegative_sum_product_first R X [the choiceType of (nat : Type)]
  [set x | p x=y] setT (fun q => (r q.2*s q.2 q.1)%R%:E)); last by move=> [x n] _; exact: hp.
rewrite nonnegative_sum_product_second; last by move=> [x n] _; exact: hp.
apply: nonnegative_sum_ext=> n _.
have he' : (fun x => (r n*s n x)%R%:E)=(fun x => (r n)%:E*(s n x)%:E).
  by apply: funext=> x; rewrite EFinM.
rewrite he' nonnegative_sum_scale //.
- by rewrite -/(fibre_nonnegative_sum _ _ _) (@fibre_characteristic_sum R X Y p (E n) (s n) (hs n) y).
- move=> x _; case: (pselect (E n x))=> h;
    [rewrite (characteristic_on_set (hs n) h)|rewrite (characteristic_off_set (hs n) h)]; exact: lee01 || exact: lexx.
Qed.
