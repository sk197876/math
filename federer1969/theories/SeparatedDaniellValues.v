(** Federer (1969), 2.5.7, p. 99: values of the residual on the separating
    function h and on functions supported in S={h>0}. These supporting
    consequences use the abstract integral representations and variation
    laws from 2.5.5, pp. 96–97. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralAlmostEquality MeasureConullZeroIntegral
  FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariationBounds
  SummableRealFunctionUP RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_real_functional_almost_equal]: equality of the
    positive variation values at h and g in Federer 2.5.7, p. 99 This is
    integral invariance under almost equality on the represented lattice. *)
Lemma represented_real_functional_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A : (X -> R) -> R)
    (f g : X -> R) :
  is_real_integral_functional mu L A -> L f -> L g ->
  measure_almost_everywhere mu [set x | f x=g x] -> A f=A g.
Proof.
move=> hi hf hg he.
have hgraph : measure_almost_equal mu (real_total_integrand f) (real_total_integrand g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  apply/real_total_integrand_graph; by rewrite hx.
have hgi := @measure_integral_almost_equal R X mu hm _ _ _ (hi f hf) hgraph.
exact: EFin_inj (measure_integral_unique hgi (hi g hg)).
Qed.

(** Source for [represented_real_functional_almost_zero]: the vanishing
    negative-variation values in Federer 2.5.7, p. 99 The source space need
    not have finite measure. *)
Lemma represented_real_functional_almost_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A : (X -> R) -> R)
    (f : X -> R) :
  is_real_integral_functional mu L A -> L f ->
  measure_almost_everywhere mu [set x | f x=0%R] -> A f=0%R.
Proof.
move=> hi hf he.
have hz : is_measure_integral mu (real_total_integrand f) 0.
  apply: (@measure_almost_zero_integral R X mu hm).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  apply/real_total_integrand_graph; by rewrite hx.
exact: EFin_inj (measure_integral_unique (hi f hf) hz).
Qed.

(** Source for [separated_daniell_positive_value]: the final identity
    nu(h)=nu+(g)>=nu(g) in Federer 2.5.7, p. 99 The almost equalities refer
    to the two auxiliary measures separately. *)
Lemma separated_daniell_positive_value (R : realType) (X : choiceType)
    (L : set (X -> R)) (A B C : (X -> R) -> R)
    (sigma nu : set X -> \bar R) (hs : is_measure sigma) (hn : is_measure nu) (g h : X -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_positive_variation L A B -> is_daniell_negative_variation L A C ->
  is_real_integral_functional sigma L B -> is_real_integral_functional nu L C ->
  positive_function_lattice L g -> positive_function_lattice L h ->
  measure_almost_everywhere sigma [set x | h x=g x] ->
  measure_almost_everywhere nu [set x | h x=0%R] ->
  A h=B g /\ (A g <= A h)%R.
Proof.
move=> hL hA hB hC hBi hCi hg hh hsg hnh.
have hBg := @represented_real_functional_almost_equal R X sigma hs L B h g hBi hh.1 hg.1 hsg.
have hCh := @represented_real_functional_almost_zero R X nu hn L C h hCi hh.1 hnh.
have he := @daniell_positive_negative_identity R X L A B C hL hA hB hC h hh.
rewrite hBg hCh subr0 in he; split=> //; rewrite he.
exact: (@daniell_positive_variation_dominates R X L A B hB g hg).
Qed.

(** Source for [separated_daniell_supported_nonnegative]: the nonnegative
    residual on f*s in Federer 2.5.7, p. 99 It suffices that the test vanish
    wherever h vanishes, since h is zero almost everywhere for the negative
    representing measure. *)
Lemma separated_daniell_supported_nonnegative (R : realType) (X : choiceType)
    (L : set (X -> R)) (A B C : (X -> R) -> R)
    (nu : set X -> \bar R) (hn : is_measure nu) (h f : X -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_positive_variation L A B -> is_daniell_negative_variation L A C ->
  is_real_integral_functional nu L C -> positive_function_lattice L f ->
  measure_almost_everywhere nu [set x | h x=0%R] ->
  (forall x, h x=0%R -> f x=0%R) -> (0 <= A f)%R.
Proof.
move=> hL hA hB hC hCi hf hh hsupport.
have hf0 : measure_almost_everywhere nu [set x | f x=0%R].
  apply: (@measure_almost_everywhere_mono R X nu hn _ _ _ hh)=> x hx; exact: hsupport x hx.
have hCf := @represented_real_functional_almost_zero R X nu hn L C f hCi hf.1 hf0.
rewrite (@daniell_positive_negative_identity R X L A B C hL hA hB hC f hf) hCf subr0.
exact: (@daniell_positive_variation_nonnegative R X L A B hL hA hB f hf).
Qed.
