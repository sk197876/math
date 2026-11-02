(** Federer (1969), 1.10.5, p. 48: in finite dimension the mass infimum is
    attained by a sum of at most dim(Sym_m V) products. The
    dimension-bounded attainment asserted by Federer is proved here from
    compactness and the project's finite-combination reduction. No
    completeness assumption on the given norm is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import LinearBasis FiniteDimension FiniteOrdinalBasis
  SymmetricAlgebra SymmetricGrading SymmetricMonomialBasis SymmetricDimension
  SymmetricFormIsomorphism RealNormUP SymmetricDecompositions SymmetricDecompositionCosts
  SymmetricProjectiveMass SymmetricProjectiveSeminorm SymmetricMassPositivity
  SymmetricMassNormingForm SymmetricUnitProducts SymmetricMassConvexHull
  FiniteBasisInnerWitness SubconvexCombinations SubconvexReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_optimal_product_decomposition]: Federer
    1.10.5, p. 48, the sentence following the mass infimum:
    the infimum is a minimum when V is finite-dimensional and the
    number of summands need not exceed dim(Sym_m V). Here m is
    positive; zero has an empty optimal decomposition. *)
Theorem symmetric_optimal_product_decomposition (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (he : is_basis e)
    m (hm : (0<m)%N) (x : symmetric_power V m) :
  exists k, exists t : 'I_k -> m.-tuple V,
    (k <= dim (finite_symmetric_power he m))%N /\
    x = \sum_i symmetric_tuple_component (t i) /\
    symmetric_projective_mass (proj1 hN) hm x = \sum_i symmetric_tuple_cost N (t i).
Proof.
case: m hm x=> [|m] hm x //.
pose mass := symmetric_projective_mass (proj1 hN) hm.
pose d := mass x.
have hM := @symmetric_projective_mass_norm R V N hN m.+1 hm.
have hd0 : 0<=d := real_seminorm_nonnegative (proj1 hM) x.
case: (eqVneq d 0)=> [hz|hnz].
- have hx : x=0 := proj2 hM x hz.
  exists 0%N, (fun _ => [tuple (0:V) | i<m.+1]); split=> //.
  by rewrite !big_ord0 hx (real_seminorm_zero (proj1 hM)).
- have hdp : 0<d by rewrite lt_def hnz hd0.
  pose y := d^-1 *: x.
  have hy1 : mass y = 1.
    rewrite /y /mass (real_seminorm_scale (proj1 hM)) normfV (ger0_norm hd0).
    exact: mulVf hnz.
  have [B [hB _]] := finite_basis_inner_product_witness he.
  have hyC := (proj1 (@symmetric_mass_unit_ball_iff_subconvex R V B hB N hN
    n e he m.+1 hm y)) (ltac:(change (mass y<=1); by rewrite hy1)).
  have [j [v [a [hv [ha [hs hy]]]]]] := hyC.
  have hb := finite_ordinal_basis (@symmetric_finite_monomial_basis R V n e he m.+1).
  have [k [w [b [hkd [hw [hb0 [hbs hvw]]]]]]] :=
    @subconvex_dimension_reduction R (symmetric_power V m.+1) _ _ hb
      (@symmetric_unit_products R V N m.+1) j v a hv ha hs.
  pose u := fun i => projT1 (cid (hw i)).
  have uP i := projT2 (cid (hw i)).
  pose t := fun i => symmetric_scale_first_tuple (d*b i) (u i).
  have hxu : x = \sum_i symmetric_tuple_component (t i).
    have hxy : d*:y=x by rewrite /y scalerA mulfV // scale1r.
    rewrite -hxy hy hvw scaler_sumr; apply: eq_bigr=> i _.
    rewrite /t symmetric_scale_first_component scalerA.
    by rewrite (proj2 (uP i)).
  have hcost i : symmetric_tuple_cost N (u i)<=1.
    apply: (@symmetric_unit_tuple_cost_bound R V N (proj1 hN) m.+1 (u i))=> l.
    apply: (proj1 (uP i)); exact: mem_tnth.
  have hupper : \sum_i symmetric_tuple_cost N (t i)<=d.
    have hh : \sum_i symmetric_tuple_cost N (t i)<=d * \sum_i b i.
      rewrite mulr_sumr; apply: ler_sum=> i _.
      rewrite /t (symmetric_tuple_cost_scale_first (proj1 hN))
        (ger0_norm (mulr_ge0 hd0 (hb0 i))).
      have hh := ler_wpM2l (mulr_ge0 hd0 (hb0 i)) (hcost i).
      by rewrite mulr1 in hh.
    apply: le_trans hh _; have hh' := ler_wpM2l hd0 hbs.
    by rewrite mulr1 in hh'.
  have hlower : d<=\sum_i symmetric_tuple_cost N (t i).
    have hh := @real_seminorm_sum R (symmetric_power V m.+1) mass (proj1 hM)
      (Finite.clone 'I_k _) (fun i => symmetric_tuple_component (t i)).
    rewrite -hxu in hh; apply: le_trans hh _.
    apply: ler_sum=> i _; exact: symmetric_projective_mass_tuple_bound.
  exists k, t; split.
  + by rewrite /finite_symmetric_power finite_basis_dimension.
  + split=> //; apply/eqP; rewrite eq_le; exact/andP.
Qed.
