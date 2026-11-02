(** Federer (1969), 2.5.6, p. 98: supremum of |mu(g)| over |g| <= f. The
    finite-bound lemmas use only abstract supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellVariationUP LatticeAdditiveFunctional VectorFunctionLattice ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_interval_supremum_upper]: real form of the
    upper-bound law supporting Federer 2.5.6, p. 98 *)
Lemma finite_interval_supremum_upper (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) f p :
  is_extended_real_supremum (daniell_interval_values L A f) p%:E ->
  forall k, lattice_positive_order_interval L f k -> A k <= p.
Proof.
move=> hs k hk; have hh : ((A k)%:E <= p%:E)%E.
  apply: (extended_real_supremum_upper hs); by exists k.
by rewrite lee_fin in hh.
Qed.

(** Source for [finite_interval_supremum_least]: real form of the
    least-upper-bound law supporting Federer 2.5.6, p. 98 *)
Lemma finite_interval_supremum_least (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) f p b :
  is_extended_real_supremum (daniell_interval_values L A f) p%:E ->
  (forall k, lattice_positive_order_interval L f k -> A k <= b) -> p <= b.
Proof.
move=> hs hb; have hh : (p%:E <= b%:E)%E.
  apply: (extended_real_supremum_least hs)=> v [k [hk ->]].
  rewrite lee_fin; exact: hb k hk.
by rewrite lee_fin in hh.
Qed.

(** Source for [symmetric_interval_parts]: positive and negative parts lie
    in [0,f] when |g| <= f, supporting the upper bound in Federer 2.5.6, p.
    98 *)
Lemma symmetric_interval_parts (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) f g :
  positive_function_lattice L f -> lattice_symmetric_order_interval L f g ->
  lattice_positive_order_interval L f (fun x => Order.max (g x) 0) /\
  lattice_positive_order_interval L f (fun x => Order.max (- g x) 0).
Proof.
move=> hf [hg hgf]; split.
- split; first exact: (@function_lattice_positive_part R X L hL g hg).
  split=> x; first by rewrite le_max lexx orbT.
  rewrite ge_max hf.2 andbT.
  exact: le_trans (ler_norm (g x)) (hgf x).
- split; first exact: (@function_lattice_negative_part R X L hL g hg).
  split=> x; first by rewrite le_max lexx orbT.
  rewrite ge_max hf.2 andbT.
  have hh := ler_norm (- g x); rewrite normrN in hh.
  exact: le_trans hh (hgf x).
Qed.

(** Source for [finite_variation_sum_upper]: upper inequality for Federer's
    absolute-value supremum in 2.5.6, p. 98 Additivity alone suffices. *)
Lemma finite_variation_sum_upper (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f p q :
  positive_function_lattice L f ->
  is_extended_real_supremum (daniell_interval_values L A f) p%:E ->
  is_extended_real_supremum (daniell_interval_values L (fun k => - A k) f) q%:E ->
  forall g, lattice_symmetric_order_interval L f g -> `|A g| <= p+q.
Proof.
move=> hf hp hq g hg.
have [hgp hgn] := @symmetric_interval_parts R X L hL.1 f g hf hg.
pose u x := Order.max (g x) 0.
pose v x := Order.max (- g x) 0.
have he : (fun x => u x-v x)=g.
  apply: funext=> x; rewrite /u /v.
  case: (leP 0 (g x))=> h.
  - by rewrite max_r ?oppr_le0 // subr0.
  - by rewrite max_l ?oppr_ge0 ?ltW // sub0r opprK.
have ha := @vector_lattice_additive_difference R X L A hL hA u v hgp.1 hgn.1.
rewrite he in ha; rewrite ha ler_norml; apply/andP; split.
- have hh := lerD (@finite_interval_supremum_upper R X L (fun k => - A k) f q hq u hgp)
    (@finite_interval_supremum_upper R X L A f p hp v hgn).
  rewrite [(- A u+A v)%R]addrC [q+p]addrC in hh.
  rewrite -[A u-A v]opprB lerN2; exact: hh.
- exact: lerD (@finite_interval_supremum_upper R X L A f p hp u hgp)
    (@finite_interval_supremum_upper R X L (fun k => - A k) f q hq v hgn).
Qed.

(** Source for [finite_variation_sum_least]: lower inequality for the
    supremum formula in Federer 2.5.6, p. 98 Two independent order intervals
    provide k-l with |k-l| <= f; no maximizer is assumed. *)
Lemma finite_variation_sum_least (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f p q b :
  is_extended_real_supremum (daniell_interval_values L A f) p%:E ->
  is_extended_real_supremum (daniell_interval_values L (fun k => - A k) f) q%:E ->
  (forall g, lattice_symmetric_order_interval L f g -> `|A g| <= b) -> p+q <= b.
Proof.
move=> hp hq hb.
have haux k : lattice_positive_order_interval L f k -> A k+q <= b.
  move=> hk.
  have hh : q <= b-A k.
    apply: (@finite_interval_supremum_least R X L (fun k => - A k) f q _ hq)=> l hl.
    rewrite lerBrDl.
    have hg := @lattice_interval_difference_symmetric R X L hL f k l hk hl.
    have hv := hb _ hg.
    rewrite (@vector_lattice_additive_difference R X L A hL hA k l hk.1 hl.1) in hv.
    exact: le_trans (ler_norm (A k-A l)) hv.
  by move: hh; rewrite lerBrDl.
have hh : p <= b-q.
  apply: (@finite_interval_supremum_least R X L A f p _ hp)=> k hk.
  rewrite lerBrDr; exact: haux k hk.
by move: hh; rewrite lerBrDr.
Qed.
