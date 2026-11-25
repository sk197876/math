(** Federer (1969), 2.5.10, p. 101: passing from the local density formulas
    to every summable test. This avoids assuming global countable support of
    either density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasureFiniteClosure MeasureCountableClosure
  MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP CountableFamilySequence
  FunctionLatticeUP FunctionLatticeSeminormUP DaniellIntegralUP ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarLpCharacteristic
  CharacteristicFunctionSealed PositivePartFunctionalDetermination
  SetSequenceDisjointification MeasureSequencePrefixes TotalScalarCutoff CutoffFunctionalAgreement
  CutoffPrefixConvergence FiniteMeasureDecompositionUP CountablyCoveredLoneSupport BoundedLoneFunctionalContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lone_functionals_determined_on_finite_pieces]: supporting
    completion of the representation argument in Federer 2.5.10, p. 101
    Agreement on each piece determines bounded L1 functionals globally. *)
Theorem lone_functionals_determined_on_finite_pieces (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (A C : (X -> R) -> R) (M N : R) :
  finite_measure_sets_countably_covered mu D B ->
  (forall j, D j -> measure_measurable mu (B j)) -> (0 <= M)%R -> (0 <= N)%R ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) C ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  (forall f, total_scalar_lp mu 1 f -> (`|C f| <= N * finite_total_scalar_lp_norm mu 1 f)%R) ->
  (forall j, D j -> cutoff_functionals_agree mu A C (B j)) ->
  forall f, total_scalar_lp mu 1 f -> A f=C f.
Proof.
move=> hcov hB hM hN hA hC hbA hbC hagree.
have [hDA hAA] := @bounded_lone_functional_continuity R X mu hm A M hM hA hbA.
have [hDC hCA] := @bounded_lone_functional_continuity R X mu hm C N hN hC hbC.
apply: (@vector_lattice_additive_positive_determination R X _ A C
  (@total_scalar_lp_vector_lattice R X mu hm 1 (lexx _)) hA.1 hC.1)=> f [hf hf0].
pose S := partial_function_nonzero_locus 0%R (total_scalar_function f).
have [E [hED [hE hnull]]] := @finite_cover_covers_countably_measurable_set R X J mu hm D B S hcov
  (countably_measurable_function_locus hf.2.2.2).
have [G [hG hGU]] := @countable_family_as_sequence X J E B hE.
pose U := \bigcup_n G n.
have hGm n : measure_measurable mu (G n).
  have [->|[j [hj ->]]] := hG n; first exact: measure_measurable_empty hm.
  exact: hB j (hED j hj).
have hUm : measure_measurable mu U := @measure_measurable_sequence_union R X mu hm G hGm.
have hcut T (hT : measure_measurable mu T) : total_scalar_lp mu 1 (total_scalar_cutoff T f).
  exact: (@total_scalar_lp_characteristic_piece R X mu hm 1 T _ f (@CharacteristicFunction.laws R X T) hT hf).
have hUg := hcut U hUm.
have heq : measure_almost_everywhere mu [set x | f x=total_scalar_cutoff U f x].
  rewrite -hGU in hnull.
  apply: (@measure_null_subset R X mu hm _ (S `\` U) _ hnull)=> x hn.
  have hxU : ~ U x.
    move=> hu; apply: hn; change (f x=total_scalar_cutoff U f x).
    by rewrite (total_scalar_cutoff_on f hu).
  split=> //; exists (f x); split=> // hx0.
  apply: hn; change (f x=total_scalar_cutoff U f x).
  by rewrite (total_scalar_cutoff_off f hxU) hx0.
have hprefix n : cutoff_functionals_agree mu A C (set_sequence_prefix G n).
  elim: n=> [|n IH].
  - rewrite set_sequence_prefix_zero; exact: (@cutoff_functionals_agree_empty R X mu hm A C hA hC).
  - rewrite set_sequence_prefix_succ; apply: (@cutoff_functionals_agree_union R X mu hm A C _ _ hA hC
      (measure_sequence_prefix_measurable hm hGm n) (hGm n) IH).
    have [->|[j [hj ->]]] := hG n; first exact: (@cutoff_functionals_agree_empty R X mu hm A C hA hC).
    exact: hagree j (hED j hj).
have hfn n := hcut _ (measure_sequence_prefix_measurable hm hGm n).
have hinc := @positive_cutoff_prefix_increases R X G f hf0.
have hla := @daniell_integral_increasing_continuity R X _ A hDA _ _ hfn hUg hinc.
have hlc := @daniell_integral_increasing_continuity R X _ C hDC _ _ hfn hUg hinc.
have he : (fun n => (A (total_scalar_cutoff (set_sequence_prefix G n) f))%:E)=
    (fun n => (C (total_scalar_cutoff (set_sequence_prefix G n) f))%:E).
  apply: funext=> n; by rewrite (hprefix n f hf).
rewrite he in hla; have hv := extended_order_limit_unique hla hlc.
have hv' : A (total_scalar_cutoff U f)=C (total_scalar_cutoff U f) by injection hv.
by rewrite (hAA f _ hf hUg heq) (hCA f _ hf hUg heq).
Qed.
