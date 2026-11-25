(** Supporting linearity of the elementary primitive calculations in Federer
    (1969), 2.6.3(2), pp. 117–118 These laws are proved from the
    finite-increment specification; they introduce no unproved calculus
    assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import UniformPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_primitive_constant]: supporting zero
    derivative of a constant primitive in the elementary
    calculations of Federer 2.6.3(2), pp. 117–118. *)
Lemma uniform_primitive_constant (R : realType) (a b c : R) :
  is_uniform_primitive_on (fun _ => 0) (fun _ => c) a b.
Proof.
move=> e he; exists 1; split=> // s u t has hsu hut htb _.
rewrite subrr mul0r subr0 normr0; apply: mulr_ge0; first exact: ltW he.
rewrite subr_ge0; exact: le_trans hsu hut.
Qed.

(** Source for [uniform_primitive_add]: supporting addition of primitive
    evaluations in Federer 2.6.3(2), pp. 117–118 *)
Lemma uniform_primitive_add (R : realType) (f F g G : R -> R) (a b : R) :
  is_uniform_primitive_on f F a b -> is_uniform_primitive_on g G a b ->
  is_uniform_primitive_on (fun x => f x+g x) (fun x => F x+G x) a b.
Proof.
move=> hF hG e he.
have he2 : 0 < e/2 by lra.
have [d1 [hd1 h1]] := hF _ he2; have [d2 [hd2 h2]] := hG _ he2.
exists (Order.min d1 d2); split; first by rewrite lt_min hd1 hd2.
move=> s u t has hsu hut htb ht.
move: ht; rewrite lt_min=> /andP[ht1 ht2].
have hF' := h1 s u t has hsu hut htb ht1.
have hG' := h2 s u t has hsu hut htb ht2.
have heq : F t+G t-(F s+G s)-(f u+g u)*(t-s) =
    (F t-F s-f u*(t-s))+(G t-G s-g u*(t-s)) by ring.
rewrite heq; apply: le_trans (ler_normD _ _) _.
have hsum := lerD hF' hG'.
have hcoef : (e/2)*(t-s)+(e/2)*(t-s)=e*(t-s) by field.
by rewrite hcoef in hsum.
Qed.

(** Source for [uniform_primitive_scale]: supporting scalar
    multiples of primitive evaluations in Federer 2.6.3(2),
    pp. 117–118, including the zero scalar. *)
Lemma uniform_primitive_scale (R : realType) (f F : R -> R) (a b c : R) :
  is_uniform_primitive_on f F a b ->
  is_uniform_primitive_on (fun x => c*f x) (fun x => c*F x) a b.
Proof.
move=> hF; case: (eqVneq c 0)=> [->|hc].
- have hf : (fun x => 0*f x) = (fun _ : R => 0) by apply: funext=> x; rewrite mul0r.
  have hG : (fun x => 0*F x) = (fun _ : R => 0) by apply: funext=> x; rewrite mul0r.
  rewrite hf hG; exact: uniform_primitive_constant.
- move=> e he.
  have hcn : 0 < `|c| by rewrite normr_gt0.
  have hec : 0 < e/`|c| by rewrite divr_gt0.
  have [d [hd hh]] := hF _ hec; exists d; split=> // s u t has hsu hut htb ht.
  have h := hh s u t has hsu hut htb ht.
  have heq : c*F t-c*F s-c*f u*(t-s)=c*(F t-F s-f u*(t-s)) by ring.
  rewrite heq normrM.
  have hmul := ler_wpM2l (normr_ge0 c) h.
  have hcoef : `|c|*(e/`|c|*(t-s))=e*(t-s) by field; rewrite normr_eq0 hc.
  by rewrite hcoef in hmul.
Qed.

(** Source for [uniform_primitive_ext]: supporting replacement
    by algebraically equal formulas on the integration interval
    in Federer 2.6.3(2), pp. 117–118. Values outside
    the interval play no role in its primitive law. *)
Lemma uniform_primitive_ext (R : realType) (f F g G : R -> R) (a b : R) :
  (forall x, a <= x <= b -> f x = g x /\ F x = G x) ->
  is_uniform_primitive_on f F a b -> is_uniform_primitive_on g G a b.
Proof.
move=> he hF e hep; have [d [hd hh]] := hF e hep.
exists d; split=> // s u t has hsu hut htb ht.
have hs : a <= s <= b by rewrite has /=; exact: le_trans hsu (le_trans hut htb).
have hu : a <= u <= b by rewrite (le_trans has hsu) /=; exact: le_trans hut htb.
have hT : a <= t <= b by rewrite htb andbT; exact: le_trans has (le_trans hsu hut).
rewrite -(he t hT).2 -(he s hs).2 -(he u hu).1.
exact: hh.
Qed.
