(** Federer (1969), 2.6.4, pp. 118–119: addition and scaling in the L1
    closure used for tensor-image density. Only linear subspace laws and
    summability of its members are assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient MeasureUP MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic
  LatticeL1ApproximationLaws RealIntegralErrorArithmetic SubspaceLoneApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Approximation.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Variable L : subspace (GRing.Lmodule.clone R (X -> R^o) _).
Hypothesis hLs : forall f, L f -> summable_real_functions mu f.

(** Source for [subspace_lone_approximable_zero]: the empty
    linear combination in the density proof of Federer 2.6.4,
    pp. 118–119. *)
Lemma subspace_lone_approximable_zero : is_subspace_lone_approximable mu L (fun _ => 0).
Proof.
split; first exact (@hLs (fun _ => 0) (subspace_zero L)).
move=> e he; exists (fun _ => 0),0; split; first exact: subspace_zero.
split=> //.
have hz : (fun _ : X => `|(0 : R)-0|)=(fun _ => (0 : R)) by apply: funext=> x; rewrite subrr normr0.
rewrite hz; exact: real_total_zero_integral hm.
Qed.

(** Source for [subspace_lone_approximable_add]: supporting
    additive closure of the tensor image's L1 closure in
    Federer 2.6.4, pp. 118–119. *)
Lemma subspace_lone_approximable_add f g :
  is_subspace_lone_approximable mu L f -> is_subspace_lone_approximable mu L g ->
  is_subspace_lone_approximable mu L (fun x => f x+g x).
Proof.
move=> [hf hfa] [hg hga]; split; first exact (@summable_real_add R X mu hm f g hf hg).
move=> d hd; have hd2 : 0<d/2 by rewrite divr_gt0 // ltr0n.
have [k [a [hk [ha had]]]] := hfa _ hd2.
have [l [b [hl [hb hbd]]]] := hga _ hd2.
have [e [he heb]] := @real_total_integral_error_add R X mu hm k f l g a b
  (@hLs k hk) hf (@hLs l hl) hg ha hb.
exists (fun x => k x+l x),e; split; first exact: subspace_add hk hl.
split=> //; have hs := ltrD had hbd; rewrite -splitr in hs; exact: le_lt_trans heb hs.
Qed.

(** Source for [subspace_lone_approximable_positive_scale]:
    supporting nonnegative scaling for the finite simple-function
    reduction in Federer 2.6.4, pp. 118–119. Zero
    scaling is handled without division by the coefficient. *)
Lemma subspace_lone_approximable_positive_scale f c : 0<=c ->
  is_subspace_lone_approximable mu L f ->
  is_subspace_lone_approximable mu L (fun x => c*f x).
Proof.
move=> hc [hf hfa]; case: (eqVneq c 0)=> hc0.
- have he : (fun x => c*f x)=(fun _ => (0 : R)) by apply: funext=> x; rewrite hc0 mul0r.
  rewrite he; exact: subspace_lone_approximable_zero.
- have hcp : 0<c by rewrite lt_neqAle eq_sym hc0 hc.
  split; first exact (@summable_real_scale R X mu hm f c hf).
  move=> d hd; have hdc : 0<d/c by rewrite divr_gt0.
  have [k [e [hk [he hed]]]] := hfa _ hdc.
  exists (fun x => c*k x),(c*e); split; first exact (@subspace_scale R _ L c k hk).
  split; first exact (@real_total_integral_error_scale R X mu hm k f e c hc he).
  have hh : c*e<c*(d/c) by rewrite ltr_pM2l.
  by rewrite mulrCA divff // mulr1 in hh.
Qed.

(** Source for [subspace_lone_approximable_negate]: supporting
    signed reduction in the density assertion of Federer 2.6.4,
    p. 119, which cites 2.4.4(6), p. 82. *)
Lemma subspace_lone_approximable_negate f : is_subspace_lone_approximable mu L f ->
  is_subspace_lone_approximable mu L (fun x => -f x).
Proof.
move=> [hf hfa]; split.
- have hi := @summable_real_scale R X mu hm f (-1) hf.
  have he : (fun x => -1*f x)=(fun x => -f x) by apply: funext=> x; rewrite mulN1r.
  by rewrite he in hi.
- move=> d hd; have [h [q [hh [hi hq]]]] := hfa d hd.
  exists (fun x => -h x),q; split; first exact: subspace_opp hh.
  split=> //.
  have he : (fun x => `|-h x- -f x|)=(fun x => `|h x-f x|).
    by apply: funext=> x; rewrite -opprD normrN.
  by rewrite he.
Qed.
End Approximation.
