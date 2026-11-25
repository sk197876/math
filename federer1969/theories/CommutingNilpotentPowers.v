(** Federer (1969), 1.8.2, p. 40: algebraic computation of the
    exterior power of the orthogonal two-form normal form. The pair
    blocks commute and square to zero. These supporting algebraic
    lemmas require commutativity only among the specified blocks.
    They reuse the elementary symmetric sums from 1.4.5, p. 20. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear AlgebraPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Powers.
Variable K : fieldType.
Variable B : algebra K.
Local Notation mul := (alg_mul B).
Local Notation hb := (alg_bilinear B).
Local Notation pow := (@algebra_power K B).
Local Notation es := (@elementary_symmetric K B).

(** Source for [commuting_square_zero_power_sum]: Federer 1.8.2,
    p. 40, supporting binomial step for commuting square-zero blocks. *)
Lemma commuting_square_zero_power_sum a b :
  mul a a = 0 -> mul b a = mul a b -> forall m,
  pow (a+b) m.+1 = pow b m.+1 + (m.+1%:R : K) *: mul a (pow b m).
Proof.
move=> ha hc; elim=> [|m ih].
- by rewrite !algebra_power1 /= alg_unitr scale1r addrC.
change (mul (a+b) (pow (a+b) m.+1) =
  mul b (pow b m.+1) + (m.+2%:R : K) *: mul a (pow b m.+1)).
rewrite ih (bilDl hb) !(bilDr hb) !(bilZr hb).
have hz : mul a (mul a (pow b m)) = 0.
  by rewrite alg_assoc ha (bil0l hb).
have hm : mul b (mul a (pow b m)) = mul a (pow b m.+1).
  by rewrite alg_assoc hc -alg_assoc.
rewrite hz scaler0 addr0 hm [mul a _ + _]addrCA.
congr (_ + _).
by rewrite -{1}(scale1r (mul a (pow b m.+1))) -scalerDl nat1r.
Qed.

(** Source for [commuting_square_zero_sum_power]: Federer 1.8.2,
    p. 40, the power of the normal-form sum is m! times the sum
    of products over m distinct blocks. Pairwise commutation suffices. *)
Theorem commuting_square_zero_sum_power (s : seq B) :
  (forall a, a \in s -> mul a a = 0) ->
  (forall a b, a \in s -> b \in s -> mul a b = mul b a) -> forall m,
  pow (\sum_(a <- s) a) m = (m`!%:R : K) *: es s m.
Proof.
elim: s => [|a s ih] hs hc [|m].
- by rewrite /= scale1r.
- by rewrite big_nil /= (bil0l hb) scaler0.
- by rewrite /= scale1r.
have ha := hs a (mem_head a s).
have ht x : x \in s -> mul x x = 0.
  move=> hx; apply: hs; by rewrite inE hx orbT.
have hct x y : x \in s -> y \in s -> mul x y = mul y x.
  move=> hx hy; apply: hc; by rewrite inE ?hx ?hy orbT.
have hca : mul (\sum_(x <- s) x) a = mul a (\sum_(x <- s) x).
  rewrite (big_morph (fun x => mul x a) (fun x y => bilDl hb x y a) (bil0l hb a))
    (big_morph (mul a) (bilDr hb a) (bil0r hb a)); apply: eq_big_seq => x hx.
  have hx' : x \in a::s by rewrite inE hx orbT.
  exact: hc x a hx' (mem_head a s).
rewrite big_cons (commuting_square_zero_power_sum ha hca)
  (ih ht hct m.+1) (ih ht hct m) (bilZr hb) scalerA factS natrM scalerDr /=.
by [].
Qed.

(** Source for [elementary_symmetric_above_length]: Federer 1.8.2,
    p. 40, supporting vanishing when there are fewer normal-form
    blocks than the requested power. *)
Lemma elementary_symmetric_above_length (s : seq B) m :
  (size s < m)%N -> es s m = 0.
Proof.
elim: s m => [|a s ih] [|m] //=.
move=> hm.
have h : (size s < m)%N := hm.
have hnext : (size s < m.+1)%N := ltn_trans h (ltnSn m).
by rewrite (ih m.+1 hnext) (ih m h) (bil0r hb) add0r.
Qed.

(** Source for [elementary_symmetric_top]: Federer 1.8.2,
    p. 40, the top elementary symmetric sum is the ordered product
    of all normal-form blocks, with the empty product equal to one. *)
Lemma elementary_symmetric_top (s : seq B) :
  es s (size s) = foldr mul (alg_one B) s.
Proof.
elim: s => [|a s ih] //=.
by rewrite elementary_symmetric_above_length ?ltnSn // ih add0r.
Qed.

(** Source for [commuting_square_zero_top_power]: Federer 1.8.2,
    p. 40, the top power of k commuting square-zero blocks equals
    k! times their ordered product. *)
Theorem commuting_square_zero_top_power (s : seq B)
    (hs : forall a, a \in s -> mul a a = 0)
    (hc : forall a b, a \in s -> b \in s -> mul a b = mul b a) :
  pow (\sum_(a <- s) a) (size s) =
    ((size s)`!%:R : K) *: foldr mul (alg_one B) s.
Proof. by rewrite (commuting_square_zero_sum_power hs hc) elementary_symmetric_top. Qed.

(** Source for [commuting_square_zero_power_vanishes]: Federer 1.8.2,
    p. 40, supporting vanishing above the number of normal-form blocks. *)
Theorem commuting_square_zero_power_vanishes (s : seq B)
    (hs : forall a, a \in s -> mul a a = 0)
    (hc : forall a b, a \in s -> b \in s -> mul a b = mul b a) m :
  (size s < m)%N -> pow (\sum_(a <- s) a) m = 0.
Proof.
move=> hm; by rewrite (commuting_square_zero_sum_power hs hc)
  (elementary_symmetric_above_length hm) scaler0.
Qed.
End Powers.
