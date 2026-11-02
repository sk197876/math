(** Federer (1969), 2.5.5, p. 97: positive homogeneity of mu+. The zero
    scalar is handled separately, so no inverse of zero is used in the
    proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra
  DaniellVariationUP DaniellVariationBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lattice_positive_order_interval_scale]: scaled admissible
    interval in the homogeneity argument of Federer 2.5.5, p. 97 *)
Lemma lattice_positive_order_interval_scale (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (c : R) (f k : X -> R) :
  0 <= c -> lattice_positive_order_interval L f k ->
  lattice_positive_order_interval L (fun x => c * f x) (fun x => c * k x).
Proof.
move=> hc [hk [hk0 hkf]]; split.
- exact: (@function_lattice_scale R X L hL c k hc hk).
- split=> x; [exact: mulr_ge0 hc (hk0 x)|exact: (@ler_wpM2l R c hc (k x) (f x) (hkf x))].
Qed.

(** Source for [daniell_positive_variation_zero]: the zero-scalar case in
    Federer 2.5.5, p. 97 *)
Lemma daniell_positive_variation_zero (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) :
  L f -> P (fun _ => 0)=0.
Proof.
move=> hf.
have hz : positive_function_lattice L (fun _ => 0).
  split; first exact: (@function_lattice_zero R X L hL f hf).
  by move=> x; exact: lexx.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@daniell_positive_variation_least R X L A P hP _ 0 hz)=> k hk.
  have he : k=(fun _ => 0).
    apply: funext=> x; apply/eqP; by rewrite eq_le hk.2.2 hk.2.1.
  by rewrite he (@daniell_integral_zero R X L A hA f hf).
- exact: (@daniell_positive_variation_nonnegative R X L A P hL hA hP _ hz).
Qed.

(** Source for [daniell_positive_variation_scale]: exact positive
    homogeneity of mu+ on L+ in Federer 2.5.5, p. 97 Both scalar zero and
    arbitrary positive real scalars are included. *)
Theorem daniell_positive_variation_scale (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (c : R) (f : X -> R) :
  0 <= c -> positive_function_lattice L f -> P (fun x => c * f x)=c * P f.
Proof.
move=> hc hf.
case: (eqVneq c 0)=> [->|hc0].
  have he : (fun x => 0 * f x)=(fun _ : X => 0) by apply: funext=> x; rewrite mul0r.
  by rewrite he mul0r (@daniell_positive_variation_zero R X L A P hL hA hP f hf.1).
have hci : 0 <= c^-1 by rewrite invr_ge0.
pose cf x := c * f x.
have hcf : positive_function_lattice L cf.
  split; first exact: (@function_lattice_scale R X L hL c f hc hf.1).
  move=> x; exact: mulr_ge0 hc (hf.2 x).
have hup : P cf <= c * P f.
  apply: (@daniell_positive_variation_least R X L A P hP cf _ hcf)=> h hh.
  have hk := @lattice_positive_order_interval_scale R X L hL c^-1 cf h hci hh.
  have he : (fun x => c^-1 * cf x)=f by apply: funext=> x; rewrite /cf mulrA mulVf // mul1r.
  rewrite he in hk.
  have hb := @daniell_positive_variation_upper R X L A P hP f _ hf hk.
  rewrite (@daniell_integral_scale R X L A hA c^-1 h hci hh.1) in hb.
  have hb' := ler_wpM2l hc hb.
  by rewrite mulrA mulfV // mul1r in hb'.
have hlo : c * P f <= P cf.
  have hb : P f <= c^-1 * P cf.
    apply: (@daniell_positive_variation_least R X L A P hP f _ hf)=> k hk.
    have hck := @lattice_positive_order_interval_scale R X L hL c f k hc hk.
    have hv := @daniell_positive_variation_upper R X L A P hP cf _ hcf hck.
    rewrite (@daniell_integral_scale R X L A hA c k hc hk.1) in hv.
    have hv' := ler_wpM2l hci hv.
    by rewrite mulrA mulVf // mul1r in hv'.
  have hb' := ler_wpM2l hc hb.
  by rewrite mulrA mulfV // mul1r in hb'.
apply/eqP; by rewrite eq_le hup hlo.
Qed.
