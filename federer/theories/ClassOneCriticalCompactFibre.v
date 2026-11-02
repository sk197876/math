(** Federer (1969), 3.2.31, p. 269: the critical-source
    fibre estimate for a class-one map on a compact set.
    Actual small symmetric rescalings and finite null-overlap
    covers prove a zero upper integral before rectifiability
    of any target fibre-threshold set is known. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormClassOneUP LinearRankAtLeast EuclideanClassZeroContinuity EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes HausdorffMeasure HausdorffFibreCutoffs HausdorffFibreCost CompactFibreMeasurability
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureNonnegativeIntegral MeasureUpperIntegralNonnegative
  CompactRescaledCoverUP CompactRescaledCoverExistence SmallExteriorCompactFibreBound
  FiniteNullOverlapFibreBound ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CriticalCompactFibre.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).
Local Notation Leb:=(@euclidean_lebesgue_measure R m).

(** Source for [class_one_critical_compact_fibre_integral_zero]:
    supporting the vanishing critical-fibre integral in Federer
    3.2.31, p. 269. For class-one maps, compact first-hit
    refinements with null ball-shell overlaps justify the finite
    sum and its exact source-mass budget. The coefficient tends
    to zero with epsilon, without dependence on the cover size.
    This lemma assumes positive target and fibre-base degree;
    degenerate degrees are handled separately by the final theorem. *)
Theorem class_one_critical_compact_fibre_integral_zero (G:X->Y)
    (D:X->Hom (R_n R m) (R_n R v)) (K:set X) k mu:
  (0<v)%N ->(0<mu)%N ->m=(k+mu)%N ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT G D ->
  compact K ->(forall x,K x ->~linear_rank_at_least (D x) mu) ->
  measure_upper_integral (@hausdorff_measure R Y mu)
    (partial_function_total (hausdorff_fibre_mass G K k))=0.
Proof.
move=>hv hmu hDim hG hK hRank.
have hCont:continuous G:=euclidean_class_zero_continuous (norm_class_one_zero hG).
pose beta:=@hausdorff_measure R Y mu.
have hb:is_measure beta:=@hausdorff_measure_is_measure R Y mu.
pose nu:=@hausdorff_measure R X k.
have hn:is_measure nu:=@hausdorff_measure_is_measure R X k.
have hLeb:=euclidean_lebesgue_is_measure R m.
have hPos (A:set X) y:0<=hausdorff_fibre_mass G A k y.
  exact (@measure_nonnegative R X nu hn (A `&` G @^-1` [set y])).
have hMass0:=@measure_nonnegative R X Leb hLeb K.
have hMassFinite:Leb K \is a fin_num.
  rewrite ge0_fin_numE //; exact:euclidean_compact_finite hK.
pose c:R:=((Num.sqrt v%:R)^+mu*2^+mu.-1)%R.
pose b:R:=@hausdorff_fibre_bound_constant R k mu 1%R.
pose M:R:=fine (Leb K).
pose B:R:=(c*b*M)%R.
have hc:(0<=c)%R:=mulr_ge0 (exprn_ge0 mu (sqrtr_ge0 _)) (exprn_ge0 mu.-1 (ler0n R 2)).
have hb0:(0<=b)%R:=@hausdorff_fibre_bound_constant_nonnegative R k mu 1%R (@ler01 R).
have hM:(0<=M)%R by rewrite /M -lee_fin fineK.
have hB:(0<=B)%R:=mulr_ge0 (mulr_ge0 hc hb0) hM.
have hUpper:measure_upper_integral beta (partial_function_total (hausdorff_fibre_mass G K k))<=0.
  apply:(@extended_upper_bound_from_scaled_errors R
    (measure_upper_integral beta (partial_function_total (hausdorff_fibre_mass G K k))) 0%R B hB).
  move=>e he.
  have [N [a [T [U [C hCover]]]]]:=@compact_rescaled_cover_exists R m v mu G D K e hG hK hRank he.
  pose E (i:'I_N):=C (val i).
  have hCompact i:compact (E i).
    exact (@rescaled_cover_compact R m v mu G D K e N a T U C hCover (val i) (ltn_ord i)).
  have hUnion:(\bigcup_(i in @setT 'I_N) E i)=K.
    rewrite -(@rescaled_cover_union R m v mu G D K e N a T U C hCover).
    apply/seteqP; split=>x [i hi hxi].
    - exists (val i)=>//; exact:ltn_ord.
    - exists (Ordinal hi)=>//.
  have hMeas i:measure_measurable Leb (E i).
    apply:(borel_regular_borel_measurable hLeb (euclidean_lebesgue_borel_regular R m)).
    apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R X) (hCompact i).
  have hOverlap i j:i!=j ->Leb (E i `&` E j)=0.
    move=>hne; apply:(@rescaled_cover_null_overlaps R m v mu G D K e N a T U C hCover
      (val i) (val j) (ltn_ord i) (ltn_ord j)).
    apply/eqP=>hij; apply:(negP hne); apply/eqP; exact:val_inj hij.
  have hI i:is_measure_integral beta (partial_function_total (hausdorff_fibre_mass G (E i) k))
      (measure_upper_integral beta (partial_function_total (hausdorff_fibre_mass G (E i) k))).
    have hMeasF:=@compact_hausdorff_fibre_mass_measurable R X Y G (E i) k mu hCont (hCompact i).
    have hp:measure_almost_everywhere beta
      (partial_extended_nonnegative_locus (partial_function_total (hausdorff_fibre_mass G (E i) k))).
      apply:(measure_almost_everywhere_mono hb _ (measure_almost_everywhere_true hb))=>y _.
      exists (hausdorff_fibre_mass G (E i) k y); split=>//; exact:hPos.
    have [hi h0]:=nonnegative_measurable_function_integral hb hMeasF hp.
    have hEq:=measure_upper_integral_unique (measure_upper_integral_specification beta _) hi.2.1.
    by rewrite hEq.
  pose q:R:=(c*e*b)%R.
  have hLocal i:measure_upper_integral beta (partial_function_total (hausdorff_fibre_mass G (E i) k))<=q%:E*Leb (E i).
    have hMajor:=@rescaled_cover_majorants R m v mu G D K e N a T U C hCover (val i) (ltn_ord i).
    have hLip:=@rescaled_cover_contractions R m v mu G D K e N a T U C hCover (val i) (ltn_ord i).
    have hBound:=@small_exterior_compact_fibre_integral_bound R m v G (E i) k mu
      (D (a (val i))) e (T (val i)) (U (val i)) hv hmu hDim he hCont (hCompact i) hMajor hLip.
    by rewrite muleA -EFinM in hBound.
  have hAll:=@finite_null_overlap_fibre_integral_bound R X Y [the finType of 'I_N]
    Leb nu beta hLeb hn hb G K E q hUnion hMeas hOverlap hI hLocal.
  apply:(le_trans hAll).
  rewrite -(fineK hMassFinite) -EFinM add0r lee_fin /q /B /M.
  by rewrite [(c*e*b)%R]mulrAC [(c*b*e*fine (Leb K))%R]mulrAC.
apply/eqP; rewrite eq_le hUpper /=.
apply:(measure_upper_integral_nonnegative hb).
apply:(measure_almost_everywhere_mono hb _ (measure_almost_everywhere_true hb))=>y _.
exists (hausdorff_fibre_mass G K k y); split=>//; exact:hPos.
Qed.
End CriticalCompactFibre.
