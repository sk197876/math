(** Private existence construction for the finite positive variation in
    Federer (1969), 2.5.5, p. 96 The project's sealed extended-real supremum
    supplies the witness; zero and the assumed finite bound prove that it is
    real. Choice extends the map arbitrarily off L+. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellIntegralAlgebra DaniellVariationUP ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_daniell_interval_supremum]: existence of the real
    value mu+(f) in Federer 2.5.5, p. 96 This is the existence proof for the
    previously stated supremum specification. *)
Lemma finite_daniell_interval_supremum (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_daniell_integral L A) (f : X -> R) :
  positive_function_lattice L f -> exists a : R,
    is_extended_real_supremum (daniell_interval_values L A f) a%:E.
Proof.
move=> [hf hf0].
pose S := daniell_interval_values L A f.
pose s := extended_real_sup S.
have h0 : S 0.
  exists (fun _ => 0%R); split.
  - split; first exact: (@function_lattice_zero R X L hL f hf).
    split; first by move=> x; exact: lexx.
    exact: hf0.
  - by rewrite (@daniell_integral_zero R X L A hA f hf).
have hs0 : 0 <= s := extended_real_sup_upper h0.
have [b hb] := @daniell_integral_order_bounded R X L A hA f hf.
have hsb : s <= b%:E.
  apply: extended_real_sup_least=> v [k [hk ->]].
  rewrite lee_fin; exact: hb k hk.
have hsfin : s \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr (0%R : R)) hs0.
  - exact: le_lt_trans hsb (ltry b).
exists (fine s); rewrite fineK //; constructor.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.

(** Source for [daniell_positive_variation_exists]: existence of the
    functional specified by the first variation formula of Federer 2.5.5, p.
    96 Values outside L+ have no mathematical role. *)
Theorem daniell_positive_variation_exists (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  exists P : (X -> R) -> R, is_daniell_positive_variation L A P.
Proof.
move=> hL hA.
have happ f : exists a : R, positive_function_lattice L f ->
    is_extended_real_supremum (daniell_interval_values L A f) a%:E.
  case: (pselect (positive_function_lattice L f))=> hf.
  - have [a ha] := @finite_daniell_interval_supremum R X L A hL hA f hf.
    by exists a.
  - by exists 0%R.
exists (fun f => projT1 (cid (happ f)))=> f hf.
exact: (projT2 (cid (happ f)) hf).
Qed.
