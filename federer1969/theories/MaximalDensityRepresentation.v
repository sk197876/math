(** Federer (1969), 2.5.7, p. 99: maximality forces P(f)=integral f*k on L+.
    Erratum p. 2, book p. 99 lines 13, 14, and 17, restricts the residual
    argument to L+. The proof below preserves that domain and proves the
    separating function's Lp membership. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP CharacteristicFunctionUP CharacteristicFunctionSealed
  CountablyMeasurableUP SummableRealFunctionUP TotalScalarLpUP TotalScalarLpClosure TotalScalarLpLattice
  TotalScalarLpNormLaws TotalScalarLpFiniteSeminorm TotalScalarLpAlmostEquality TotalScalarSupport
  TotalScalarLpCharacteristic TotalScalarPairingValue TotalLpPairingBound LpConjugatePair
  LpDominatedDensityFamily PositivePairingAlmostOrder SmallFullSupportDualWitness LpDensityResidual
  SeparatedDaniellValues LpDensityPatch MaximalDensityPatchNull DominatedDensityMaximizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [maximal_dominated_density_represents]: the complete
    maximality contradiction in Federer 2.5.7, p. 99 The candidate's almost
    maximality is supplied by DominatedDensityMaximizer.v. *)
Theorem maximal_dominated_density_represents (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (M : R) (k : X -> R) :
  is_lp_conjugate_pair p q -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  lp_dominated_density_family mu p q P k ->
  (forall u, lp_dominated_density_family mu p q P u ->
    measure_almost_everywhere mu [set x | (k x <= u x)%R] ->
    ~ (0 < mu [set x | (k x < u x)%R])) ->
  forall g, positive_function_lattice (total_scalar_lp mu p) g -> P g=total_scalar_pairing mu g k.
Proof.
move=> hpq hM hP hP0 hPb hk hmax g hg.
apply/eqP; rewrite eq_le (hk.2.2 g hg) andbT leNgt; apply/negP=> hdefect.
have hgi := (@total_lp_pairing_specification_and_bound R X mu hm p q g k hpq hg.1 hk.1).1.
have hj0 := @nonnegative_total_pairing_value R X mu hm g k
  (ex_intro _ (total_scalar_pairing mu g k) hgi) hg.2 hk.2.1.
have hNg : 0 < total_scalar_lp_norm mu p g.
  have hn0 := @total_scalar_lp_norm_nonnegative R X mu hm p g hg.1.1 hg.1.2.1.
  rewrite lt_neqAle eq_sym hn0 andbT; apply/eqP=> hz.
  have hb := hPb g hg; rewrite /finite_total_scalar_lp_norm hz /= mulr0 in hb.
  have hle := le_trans hb hj0; by rewrite ltNge hle in hdefect.
have hd : (0 < P g-total_scalar_pairing mu g k)%R by rewrite subr_gt0.
have [r [hr [hr0 [hsupport hsmall]]]] := @small_positive_full_support_dual_witness R X mu hm p q g
  (P g-total_scalar_pairing mu g k)%R hpq hg.1 hg.2 hNg hd.
pose w x := (k x+r x)%R.
have hw := @total_scalar_lp_add R X mu hm q k r hk.1 hr.
have hw0 x : (0 <= w x)%R := addr_ge0 (hk.2.1 x) (hr0 x).
pose A := lp_density_residual mu P w.
have hA := @lp_density_residual_daniell R X mu hm p q P w hpq hP hw hw0.
pose L := positive_function_lattice (total_scalar_lp mu p).
have hL := positive_function_lattice_laws (@total_scalar_lp_vector_lattice R X mu hm p (lp_conjugate_pair_admissible hpq).1).1.
have hAg : (0 < A g)%R.
  have hkg := (@total_lp_pairing_specification_and_bound R X mu hm q p k g (lp_conjugate_pair_symmetric hpq) hk.1 hg.1).1.
  have hrg := (@total_lp_pairing_specification_and_bound R X mu hm q p r g (lp_conjugate_pair_symmetric hpq) hr hg.1).1.
  rewrite /A /lp_density_residual (@total_scalar_pairing_add_right R X mu hm g k r
    (ex_intro _ (total_scalar_pairing mu k g) hkg) (ex_intro _ (total_scalar_pairing mu r g) hrg)).
  rewrite subr_gt0 -ltrBrDl.
  exact (andP hsmall).2.
have [B [C [sigma [nu [h [hB [hC [hsm [hn [hBi [hCi [hrep [hh [hb [hsg hnh]]]]]]]]]]]]]]] :=
  @lp_density_residual_separation R X mu hm p q P w g hpq hP hw hw0 hg.
pose S := [set x | h x <> 0%R].
have hS : measure_measurable mu S.
  have he : S=partial_function_nonzero_locus 0%R (total_scalar_function h).
    apply/seteqP; split=> x hx; first by exists (h x); split.
    have [y [hy hy0]] := hx; have he : h x=y := hy.
    change (h x <> 0%R); by rewrite he.
  rewrite he; exact: (@total_scalar_nonzero_locus_measurable R X mu hm h hh.1.2.1).
pose s := @CharacteristicFunction.value R X S.
have hs : is_characteristic_function S s := @CharacteristicFunction.laws R X S.
have hpatch : lp_dominated_density_family mu p q P (fun x => (k x+r x*s x)%R).
  apply: (@lp_density_patch_admissible R X mu hm p q P S s k r hpq hP hs hS hk hr hr0)=> f hf.
  have hfs := (@positive_lp_characteristic_pieces R X mu hm p S s f hs hS hf).1.
  have hffs : positive_function_lattice L (fun x => (f x*s x)%R) by split=> //; exact: hfs.2.
  apply: (@separated_daniell_supported_nonnegative R X L A B C nu hn h _ hL hA hB hC hCi hffs hnh)=> x hx.
  have hxS : ~ S x by move=> hne; exact: hne hx.
  by rewrite (characteristic_off_set hs hxS) mulr0.
have hrS x : S x -> (0 < r x)%R.
  move=> hx; apply: (hsupport x).2.
  have hhpos : (0 < h x)%R.
    rewrite lt_neqAle eq_sym (andP (hb x)).1 andbT; exact/eqP.
  exact: lt_le_trans hhpos (andP (hb x)).2.
have hnull := @maximal_density_admissible_patch_null R X mu hm p q P S s k r hs hr0 hrS hmax hpatch.
have hhzero : measure_almost_everywhere mu [set x | h x=0%R] := hnull.
have hN := @total_scalar_lp_almost_zero_norm R X mu hm p h hh.1 hhzero.
have hPh : P h=0%R.
  have hbP := hPb h hh; rewrite /finite_total_scalar_lp_norm hN /= mulr0 in hbP.
  apply/eqP; by rewrite eq_le hbP hP0.
have hJh : total_scalar_pairing mu h w=0%R.
  have hj := (@total_lp_pairing_specification_and_bound R X mu hm p q h w hpq hh.1 hw).2.
  rewrite /finite_total_scalar_lp_norm hN /= mul0r in hj.
  apply/eqP; rewrite -normr_eq0 eq_le hj normr_ge0; by [].
have hAh : A h=0%R by rewrite /A /lp_density_residual hPh hJh subrr.
have hgg : positive_function_lattice L g by split=> //; exact: hg.2.
have hhh : positive_function_lattice L h by split=> //; exact: hh.2.
have [_ hle] := @separated_daniell_positive_value R X L A B C sigma nu hsm hn g h
  hL hA hB hC hBi hCi hgg hhh hsg hnh.
rewrite hAh in hle; by rewrite ltNge hle in hAg.
Qed.

(** Source for [positive_lp_functional_density]: existence of the
    representing nonnegative density for the positive variation in Federer
    2.5.7, pp. 98–99 This combines actual maximality and the residual
    contradiction for all three exponent pairs and the zero measure. *)
Theorem positive_lp_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (M : R) :
  is_lp_conjugate_pair p q -> (q=+oo -> measure_countably_measurable mu setT) -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  exists k : X -> R, total_scalar_lp mu q k /\ (forall x, (0 <= k x)%R) /\
    forall f, positive_function_lattice (total_scalar_lp mu p) f -> P f=total_scalar_pairing mu f k.
Proof.
move=> hpq hX hM hP hP0 hPb.
have [k [hk hmax]] := @dominated_density_maximal_member R X mu hm p q P M hpq hX hM hP hP0 hPb.
exists k; split; first exact: hk.1.
split; first exact: hk.2.1.
exact: (@maximal_dominated_density_represents R X mu hm p q P M k hpq hM hP hP0 hPb hk hmax).
Qed.
