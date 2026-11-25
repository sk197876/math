(** Federer (1969), 2.5.7, p. 99: define the residual nu(f)=mu+(f)-integral
    f(k+ + r), and apply 2.5.5 on L+. Erratum p. 2, book p. 99 lines 13, 14,
    and 17, explicitly restricts this step to L+. The general nonnegative
    density k below will later be k+ + r. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureIntegralUP FunctionLatticeUP FunctionLatticeLaws
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellVariationUP DaniellRepresentation RealIntegralFunctionalUP
  SummableRealFunctionUP TotalScalarLpUP TotalScalarLpLattice TotalScalarPairingValue
  TotalLpPairingBound LpConjugatePair TotalPositivePairingDaniell DaniellMonotoneDifference
  LpSeparatedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_density_residual]: direct residual formula in Federer
    2.5.7, p. 99, corrected to L+ by erratum p. 2, lines 13–14 *)
Definition lp_density_residual (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P : (X -> R) -> R) (k f : X -> R) : R :=
  (P f-total_scalar_pairing mu f k)%R.

(** Source for [lp_density_residual_daniell]: all four Daniell laws for the
    residual of Federer 2.5.7, p. 99 Ordinary increasing continuity follows
    by subtracting the two monotone integral limits. *)
Theorem lp_density_residual_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p q ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  total_scalar_lp mu q k -> (forall x, (0 <= k x)%R) ->
  is_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) (lp_density_residual mu P k).
Proof.
move=> hpq hP hk hk0.
have hL := positive_function_lattice_laws (@total_scalar_lp_vector_lattice R X mu hm p (lp_conjugate_pair_admissible hpq).1).1.
apply: (@difference_of_monotone_daniell_integrals R X _ P _ hL hP).
apply: (@nonnegative_pairing_monotone_daniell R X mu hm _ k hL hk0)=> f hf.
exists (total_scalar_pairing mu f k).
exact: (@total_lp_pairing_specification_and_bound R X mu hm p q f k hpq hf.1 hk).1.
Qed.

(** Source for [lp_density_residual_separation]: the measures and separating
    h obtained from 2.5.5 in Federer 2.5.7, p. 99 The conclusion explicitly
    proves h in L+ using its domination by g, while preserving both
    auxiliary almost-everywhere separation laws. *)
Theorem lp_density_residual_separation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (k g : X -> R) :
  is_lp_conjugate_pair p q ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  total_scalar_lp mu q k -> (forall x, (0 <= k x)%R) ->
  positive_function_lattice (total_scalar_lp mu p) g ->
  exists (B C : (X -> R) -> R) (sigma nu : set X -> \bar R) (h : X -> R),
    is_daniell_positive_variation (positive_function_lattice (total_scalar_lp mu p)) (lp_density_residual mu P k) B /\
    is_daniell_negative_variation (positive_function_lattice (total_scalar_lp mu p)) (lp_density_residual mu P k) C /\
    is_measure sigma /\ is_measure nu /\
    is_real_integral_functional sigma (positive_function_lattice (total_scalar_lp mu p)) B /\
    is_real_integral_functional nu (positive_function_lattice (total_scalar_lp mu p)) C /\
    (forall f, positive_function_lattice (total_scalar_lp mu p) f -> exists a b : R,
      is_measure_integral sigma (real_total_integrand f) a%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E /\ lp_density_residual mu P k f=(a-b)%R) /\
    positive_function_lattice (total_scalar_lp mu p) h /\
    (forall x, (0 <= h x <= g x)%R) /\
    measure_almost_everywhere sigma [set x | h x=g x] /\
    measure_almost_everywhere nu [set x | h x=0%R].
Proof.
move=> hpq hP hk hk0 hg.
pose L := positive_function_lattice (total_scalar_lp mu p).
have hL := positive_function_lattice_laws (@total_scalar_lp_vector_lattice R X mu hm p (lp_conjugate_pair_admissible hpq).1).1.
have hD := @lp_density_residual_daniell R X mu hm p q P k hpq hP hk hk0.
have hne : exists f, L f by exists g.
have [B [C [sigma [nu [hB [hC [hs [hn [_ [_ [hBi [hCi [hrep hsep]]]]]]]]]]]]] :=
  @daniell_integral_representation R X L (lp_density_residual mu P k) hL hD hne.
have hgg : positive_function_lattice L g by split=> //; exact: hg.2.
have [u [h [hu [hb [hl [hsg hnh]]]]]] := hsep g hgg.
have hmem := @lp_separating_lower_limit_member R X mu hm p g h u hg hu hb hl.
exists B,C,sigma,nu,h.
split; first exact: hB.
split; first exact: hC.
split; first exact: hs.
split; first exact: hn.
split.
- move=> f hf; apply: hBi; by split=> //; exact: hf.2.
split.
- move=> f hf; apply: hCi; by split=> //; exact: hf.2.
split; first exact: hrep.
split; first exact: hmem.
split; first exact: hb.
by split.
Qed.
