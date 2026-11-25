(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear AlgebraTensor WordAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: powers and the elementary symmetric expansion used
    to compute Gamma(f)^m/m!. These lemmas apply directly to the
    associative algebra structure of 1.2; no matrix representation is used. *)
Section Powers.
Variable K : fieldType.
Variable B : algebra K.
Local Notation mul := (alg_mul B).
Local Notation one := (alg_one B).
Local Notation hb := (alg_bilinear B).
(** Source for [algebra_power]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Definition or construction used to formalise this passage. *)
Fixpoint algebra_power (x : B) (m : nat) : B :=
  if m is k.+1 then mul x (algebra_power x k) else one.
(** Source for [algebra_power0]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma algebra_power0 x : algebra_power x 0 = one. Proof. by []. Qed.
(** Source for [algebra_power1]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma algebra_power1 x : algebra_power x 1 = x.
Proof. exact: alg_unitr. Qed.
(** Source for [algebra_power_add]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma algebra_power_add x m n :
  algebra_power x (m+n) = mul (algebra_power x m) (algebra_power x n).
Proof. by elim: m => [|m ih] /=; rewrite ?alg_unitl ?ih ?alg_assoc. Qed.
(** Source for [algebra_power_scale]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma algebra_power_scale c x m :
  algebra_power (c *: x) m = c ^+ m *: algebra_power x m.
Proof.
elim: m => [|m ih] /=; first by rewrite expr0 scale1r.
by rewrite ih (bilZl hb) (bilZr hb) scalerA exprS.
Qed.
Hypothesis hc : commutative mul.
(** Source for [square_zero_power_sum]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma square_zero_power_sum a b : mul a a = 0 -> forall m,
  algebra_power (a+b) m.+1 = algebra_power b m.+1 +
    (m.+1%:R : K) *: mul a (algebra_power b m).
Proof.
move=> ha; elim=> [|m ih].
- by rewrite !algebra_power1 /= alg_unitr scale1r addrC.
change (mul (a+b) (algebra_power (a+b) m.+1) =
  mul b (algebra_power b m.+1) +
    (m.+2%:R : K) *: mul a (algebra_power b m.+1)).
rewrite ih (bilDl hb) !(bilDr hb) !(bilZr hb).
have hz : mul a (mul a (algebra_power b m)) = 0.
  by rewrite alg_assoc ha (bil0l hb).
have hm : mul b (mul a (algebra_power b m)) =
    mul a (algebra_power b m.+1).
  by rewrite alg_assoc (hc b a) -alg_assoc.
rewrite hz scaler0 addr0 hm.
rewrite [mul a _ + _]addrCA.
congr (_ + _).
by rewrite -{1}(scale1r (mul a (algebra_power b m.+1))) -scalerDl nat1r.
Qed.

(** Source for [elementary_symmetric]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Definition or construction used to formalise this passage. *)
Fixpoint elementary_symmetric (s : seq B) (m : nat) : B :=
  match m, s with
  | 0, _ => one
  | k.+1, a :: t => elementary_symmetric t k.+1 + mul a (elementary_symmetric t k)
  | k.+1, [::] => 0
  end.
(** Source for [square_zero_sum_power]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Theorem square_zero_sum_power (s : seq B) :
  (forall a, a \in s -> mul a a = 0) -> forall m,
  algebra_power (\sum_(a <- s) a) m = (m`!%:R : K) *: elementary_symmetric s m.
Proof.
elim: s => [|a s ih] hs [|m].
- by rewrite /= scale1r.
- by rewrite big_nil /= (bil0l hb) scaler0.
- by rewrite /= scale1r.
rewrite big_cons (@square_zero_power_sum a (\sum_(x <- s) x) (hs a (mem_head a s)) m).
have ht x : x \in s -> mul x x = 0.
  move=> hx; apply: hs; by rewrite inE hx orbT.
rewrite (ih ht m.+1) (ih ht m) (bilZr hb) scalerA.
rewrite factS natrM scalerDr /=.
by [].
Qed.
End Powers.
