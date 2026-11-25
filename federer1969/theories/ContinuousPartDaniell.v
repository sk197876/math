(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext
  AbsoluteContinuousPartUP AbsoluteContinuousPart MeasureAbsoluteContinuity ContinuousPartDecompositionUP
  ContinuousPartDecomposition ContinuousPartLinfinity FiniteMeasureEssentialBoundIntegrable
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpZeroCriterion TotalEssentialNormBound
  MeasureEssentialNorm MeasureEssentialNormUP SummableRealFunctionUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureConullZeroIntegral
  FunctionLatticeUP VectorFunctionLattice RealIntegralFunctionalUP RealIntegralFunctional
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum DaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_linfinity_summable]: supporting
    well-definedness of mu(f)=integral f dpsi_phi in Federer
    2.9.10, p. 157. The printed finite psi(X) hypothesis
    gives finite continuous-part total mass. An essential bound
    transfers through absolute continuity and yields a finite integral. *)
Lemma continuous_part_linfinity_summable (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi -> psi setT< +oo ->
  total_scalar_lp phi +oo `<=` summable_real_functions (measure_continuous_part psi phi).
Proof.
move=> hphi hpsi hfinite f hf.
have hmphi := derivation_measure_law hphi.
have [B [hB _]] := @measure_continuous_part_decomposition R X phi psi hphi hpsi.
have hgamma := continuous_decomposition_class hB.
have hmgamma := derivation_measure_law hgamma.
have hac := continuous_decomposition_absolute hB.
have htot : measure_continuous_part psi phi setT< +oo.
  exact: le_lt_trans (@measure_continuous_part_le R X psi phi hmphi
    (derivation_measure_borel_regular hpsi) setT) hfinite.
pose M := fine (total_scalar_lp_norm phi +oo f).
have hnorm : total_scalar_lp_norm phi +oo f \is a fin_num.
  rewrite (ge0_fin_numE (@measure_essential_norm_nonnegative R X R phi
    (fun y => `|y|%R) (total_scalar_function f))); exact: hf.2.2.1.
have he : total_scalar_lp_norm phi +oo f=M%:E by rewrite /M fineK.
have hM : (0<=M)%R.
  have h := @measure_essential_norm_nonnegative R X R phi (fun y => `|y|%R) (total_scalar_function f).
  change (is_true (0<=total_scalar_lp_norm phi +oo f)) in h.
  by move: h; rewrite he lee_fin.
have hb := @total_essential_norm_almost_bound R X phi hmphi f M hf ltac:(by rewrite he).
have hbg : measure_almost_everywhere (measure_continuous_part psi phi) [set x | (`|f x|<=M)%R].
  exact: hac _ hb.
apply: (@finite_measure_essentially_bounded_summable R X _ f M hmgamma htot hM _ hbg).
exact: continuous_part_measurable_function hphi hpsi hf.2.1.
Qed.

(** Source for [continuous_part_daniell_functional_exists]: direct
    construction by proved existence of the functional mu in the
    second observation of Federer 2.9.10, p. 157. Its interface
    specifies actual integrals on total L-infinity(phi), the monotone
    Daniell laws, and null-norm annihilation needed for corrected
    2.5.8 (erratum p. 2, book p. 100 lines 3 and 5).
    Ambient values off the stated lattice are not used. *)
Theorem continuous_part_daniell_functional_exists (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi -> psi setT< +oo ->
  exists mu : (X -> R) -> R,
    is_real_integral_functional (measure_continuous_part psi phi) (total_scalar_lp phi +oo) mu /\
    is_monotone_daniell_integral (total_scalar_lp phi +oo) mu /\
    is_daniell_integral (total_scalar_lp phi +oo) mu /\
    (forall f, total_scalar_lp phi +oo f -> total_scalar_lp_norm phi +oo f=0 -> mu f=0%R).
Proof.
move=> hphi hpsi hfinite.
have hsum := @continuous_part_linfinity_summable R X phi psi hphi hpsi hfinite.
pose mu := @lattice_measure_integral R X (measure_continuous_part psi phi) (total_scalar_lp phi +oo) hsum.
have hrep := @lattice_measure_integral_specification R X (measure_continuous_part psi phi)
  (total_scalar_lp phi +oo) hsum.
have [B [hB _]] := @measure_continuous_part_decomposition R X phi psi hphi hpsi.
have hmgamma := derivation_measure_law (continuous_decomposition_class hB).
have hmphi := derivation_measure_law hphi.
have hL := (@total_scalar_lp_vector_lattice R X phi hmphi +oo (leey _)).1.
have hmon := @summable_sublattice_integral_laws R X (measure_continuous_part psi phi) hmgamma _ hsum hL.
exists mu; split=> //; split=> //; split.
- exact: monotone_daniell_integral_is_daniell hmon.
- move=> f hf hzero.
  have hz := @total_scalar_lp_zero_norm_almost_zero R X phi hmphi +oo f hf hzero.
  have hac := continuous_decomposition_absolute hB.
  have hzg : measure_almost_everywhere (measure_continuous_part psi phi) [set x | f x=0%R] :=
    hac _ hz.
  have hi : is_measure_integral (measure_continuous_part psi phi) (real_total_integrand f) 0.
    apply: (@measure_almost_zero_integral R X _ hmgamma).
    apply: (@measure_almost_everywhere_mono R X _ hmgamma _ _ _ hzg)=> x hx.
    apply/real_total_integrand_graph; by rewrite hx.
  have he := @measure_integral_unique R X (measure_continuous_part psi phi) _ (mu f)%:E 0 (hrep f hf) hi.
  by injection he.
Qed.
