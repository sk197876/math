(** Federer (1969), 2.5.9, p. 100: the domination hypothesis makes the
    functional Lipschitz for L1 distance. L need not be closed under
    negation; subtracting min(f,g) gives two nonnegative members of L.
    Neither passage states this particular difference estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra
  MonotoneDaniellIntegralUP RealIntegralAbsoluteMinimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lattice_absolute_difference_member]: supporting
    lattice fact for Federer 2.5.9, p. 100. Absolute
    differences belong to L even when signed differences do not. *)
Lemma lattice_absolute_difference_member (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f g : X -> R) :
  L f -> L g -> L (fun x => `|f x-g x|).
Proof.
move=> hf hg.
have hm := @function_lattice_minimum R X L hL f g hf hg.
have hmf : function_le (fun x => Order.min (f x) (g x)) f by move=> x; rewrite ge_min lexx.
have hmg : function_le (fun x => Order.min (f x) (g x)) g by move=> x; rewrite ge_min lexx orbT.
have hp := @function_lattice_ordered_difference R X L hL _ f hm hf hmf.
have hq := @function_lattice_ordered_difference R X L hL _ g hm hg hmg.
have hh := @function_lattice_add R X L hL _ _ hp hq.
have he : (fun x => (f x-Order.min (f x) (g x))+(g x-Order.min (f x) (g x)))=
    (fun x => `|f x-g x|).
  apply: funext=> x; rewrite real_absolute_difference_minimum mulr_natl mulr2n opprD.
  by rewrite addrACA addrA.
by rewrite he in hh.
Qed.

(** Source for [lattice_dominated_difference_bound]: the
    quantitative continuity needed in Federer 2.5.9, p. 100,
    before applying corrected positive density. No extension or
    representation of the signed functional is assumed. *)
Lemma lattice_dominated_difference_bound (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (A F : (X -> R) -> R) :
  is_daniell_integral L A -> is_monotone_daniell_integral L F ->
  (forall f, L f -> `|A f| <= F (fun x => `|f x|)) ->
  forall f g, L f -> L g -> `|A f-A g| <= F (fun x => `|f x-g x|).
Proof.
move=> hA hF hb f g hf hg.
pose u x := Order.min (f x) (g x).
pose p x := f x-u x.
pose q x := g x-u x.
have hu : L u := @function_lattice_minimum R X L hL f g hf hg.
have huf : function_le u f by move=> x; rewrite /u ge_min lexx.
have hug : function_le u g by move=> x; rewrite /u ge_min lexx orbT.
have hp : L p := @function_lattice_ordered_difference R X L hL u f hu hf huf.
have hq : L q := @function_lattice_ordered_difference R X L hL u g hu hg hug.
have hp0 x : 0 <= p x by rewrite /p subr_ge0; exact: huf.
have hq0 x : 0 <= q x by rewrite /q subr_ge0; exact: hug.
have hpabs : (fun x => `|p x|)=p by apply: funext=> x; exact: ger0_norm (hp0 x).
have hqabs : (fun x => `|q x|)=q by apply: funext=> x; exact: ger0_norm (hq0 x).
have hep : A p=A f-A u := @daniell_integral_ordered_difference R X L A hL hA f u hf hu huf.
have heq : A q=A g-A u := @daniell_integral_ordered_difference R X L A hL hA g u hg hu hug.
have hd : A f-A g=A p-A q by rewrite hep heq opprB addrA subrK.
have hpb := hb p hp; rewrite hpabs in hpb.
have hqb := hb q hq; rewrite hqabs in hqb.
have he : (fun x => p x+q x)=(fun x => `|f x-g x|).
  apply: funext=> x; rewrite /p /q /u real_absolute_difference_minimum mulr_natl mulr2n opprD.
  by rewrite addrACA addrA.
rewrite hd; apply: le_trans (ler_normB (A p) (A q)) _.
have hh := lerD hpb hqb.
have hsum := @monotone_daniell_integral_add R X L F hF p q hp hq.
rewrite he in hsum; by rewrite -hsum in hh.
Qed.
