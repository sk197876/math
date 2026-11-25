(** Federer (1969), 4.1.8, p. 361: compact finiteness
    of the original product of the two Radon variation
    measures. Reuse projection compactness, the measurable
    rectangle bound of 2.6.1, p. 115, and the
    original Radon compact-finiteness laws of 2.2.5. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic ProductMeasure RadonMeasureUP RadonBorelRegularity
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_product_compact_finite]: the product
    of two original Radon measures is finite on every
    compact product-domain set, supporting the representation
    in Federer 4.1.8, p. 361. Neither factor
    is assumed finite on the whole space. *)
Theorem radon_product_compact_finite (R:realType) (X Y:topologicalType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta)
    (hRA:is_radon_measure alpha) (hRB:is_radon_measure beta)
    (K:set (X*Y)):
  compact K->product_measure hAlpha hBeta K< +oo.
Proof.
move=>hK.
pose A:=(@fst X Y) @` K.
pose B:=(@snd X Y) @` K.
have hA:compact A.
  apply:continuous_compact hK;exact:continuous_subspaceT (@first_projection_continuous X Y).
have hB:compact B.
  apply:continuous_compact hK;exact:continuous_subspaceT (@second_projection_continuous X Y).
have hAFinite:alpha A< +oo:=radon_compact_finite hRA hA.
have hBFinite:beta B< +oo:=radon_compact_finite hRB hB.
have hANonnegative:0<=alpha A:=measure_nonnegative hAlpha A.
have hANumber:alpha A \is a fin_num by rewrite (ge0_fin_numE hANonnegative).
have hFinite:alpha A*beta B< +oo:=lte_mul_pinfty hANonnegative hANumber hBFinite.
have hCover:K `<=` A `*` B.
  move=>z hz;split;[by exists z|by exists z].
have hBound:=@product_measure_rectangle_bound R X Y alpha beta hAlpha hBeta A B
  (radon_compact_measurable hAlpha hRA hA) (radon_compact_measurable hBeta hRB hB).
exact:(le_lt_trans (le_trans (measure_mono (product_measure_is_measure hAlpha hBeta) hCover) hBound) hFinite).
Qed.
