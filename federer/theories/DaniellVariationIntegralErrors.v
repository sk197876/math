(** Federer (1969), 2.5.5, p. 97: the two displayed L1 errors are bounded by
    mu+(f)-mu(g_n), which tends to zero. This module supplies actual finite
    integral values, not only bounds on upper integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra DaniellVariationUP DaniellVariationBounds
  DaniellVariationApproximation RealIntegralFunctionalUP SummableRealFunctionUP SummableRealArithmetic
  MeasureUP MeasureIntegralUP RealSequenceLimitArithmetic RealScalarOrderLimits RealErrorOrderLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_variation_positive_error_integral]: first error
    identity in Federer 2.5.5, p. 97 The absolute difference is f-k because
    k lies between zero and f. *)
Lemma daniell_variation_positive_error_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (P : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hmu : is_real_integral_functional mu (positive_function_lattice L) P) (f k : X -> R) :
  positive_function_lattice L f -> lattice_positive_order_interval L f k ->
  is_measure_integral mu (real_total_integrand (fun x => `|k x-f x|%R)) (P f-P k)%R%:E.
Proof.
move=> hf hk.
have hi := @real_total_integral_subtract R X mu hm f k (P f) (P k)
  (hmu f hf) (hmu k (conj hk.1 hk.2.1)).
have he : (fun x => `|k x-f x|%R)=(fun x => (f x-k x)%R).
  apply: funext=> x; rewrite ler0_norm ?opprB // subr_le0; exact: hk.2.2.
by rewrite he.
Qed.

(** Source for [daniell_variation_negative_error_integral]: second error
    identity in Federer 2.5.5, p. 97 The absolute value equals k everywhere. *)
Lemma daniell_variation_negative_error_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (Q : (X -> R) -> R)
    (nu : set X -> \bar R)
    (hnu : is_real_integral_functional nu (positive_function_lattice L) Q) (f k : X -> R) :
  lattice_positive_order_interval L f k ->
  is_measure_integral nu (real_total_integrand (fun x => `|k x|%R)) (Q k)%:E.
Proof.
move=> hk; have he : (fun x => `|k x|%R)=k.
  apply: funext=> x; rewrite ger0_norm //; exact: hk.2.1.
rewrite he; exact: hnu k (conj hk.1 hk.2.1).
Qed.

(** Source for [daniell_variation_error_bounds]: both real error bounds in
    Federer 2.5.5, p. 97 These hold without regularity of the measures,
    since they follow from the variation laws alone. *)
Lemma daniell_variation_error_bounds (R : realType) (X : Type)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (hQ : is_daniell_negative_variation L A Q)
    (f k : X -> R) : positive_function_lattice L f -> lattice_positive_order_interval L f k ->
  (0 <= P f-P k <= P f-A k)%R /\ (0 <= Q k <= P f-A k)%R.
Proof.
move=> hf hk; have hkp : positive_function_lattice L k := conj hk.1 hk.2.1.
have hmono := @daniell_positive_variation_monotone R X L A P hP k f hkp hf hk.2.2.
have hdom := @daniell_positive_variation_dominates R X L A P hP k hkp.
have hqpos : (0 <= Q k)%R.
  have hqdom := @daniell_positive_variation_upper R X L (fun h => (- A h)%R) Q hQ k
    (fun _ => 0%R) hkp.
  have hz : lattice_positive_order_interval L k (fun _ => 0%R).
    split; first exact: (@function_lattice_zero R X L hL k hk.1).
    split; [by move=> x; exact: lexx|exact: hk.2.1].
  have hh := hqdom hz; by rewrite (@daniell_integral_zero R X L A hA k hk.1) oppr0 in hh.
split.
- by rewrite subr_ge0 hmono /= lerD2l lerN2.
- apply/andP; split; first exact: hqpos.
  have hid := @daniell_positive_negative_identity R X L A P Q hL hA hP hQ k hkp.
  have hval : Q k=(P k-A k)%R by rewrite hid opprB addrCA subrr addr0.
  by rewrite hval lerD2r.
Qed.

(** Source for [daniell_variation_two_error_limits]: simultaneous vanishing
    of the two L1 errors in Federer 2.5.5, p. 97 The single selected
    sequence is bounded pointwise by f on every point of X. *)
Theorem daniell_variation_two_error_limits (R : realType) (X : Type)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (hQ : is_daniell_negative_variation L A Q)
    (f : X -> R) : positive_function_lattice L f -> exists g : nat -> X -> R,
    (forall n, lattice_positive_order_interval L f (g n)) /\
    extended_order_limit (fun n => (P f-P (g n))%R%:E) 0 /\
    extended_order_limit (fun n => (Q (g n))%:E) 0.
Proof.
move=> hf; have [g [hg hAg]] := @daniell_variation_approximating_sequence R X L A P hP f hf.
have hd := @real_sequence_limit_subtract R (fun _ => P f) (fun n => A (g n))
  (P f) (P f) (@real_constant_order_limit R (P f)) hAg.
rewrite subrr in hd.
have hb n := @daniell_variation_error_bounds R X L A P Q hL hA hP hQ f (g n) hf (hg n).
exists g; split; first exact: hg.
split.
- apply: (@real_integral_error_comparison_limit R (fun n => (P f-P (g n))%R)
    (fun n => (P f-A (g n))%R) 0%R _ hd)=> n.
  have /andP[hn hp] := (hb n).1; by rewrite subr0 ger0_norm.
- apply: (@real_integral_error_comparison_limit R (fun n => Q (g n))
    (fun n => (P f-A (g n))%R) 0%R _ hd)=> n.
  have /andP[hn hp] := (hb n).2; by rewrite subr0 ger0_norm.
Qed.
