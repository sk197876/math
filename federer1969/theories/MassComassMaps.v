(** Federer (1969), 1.8.1, p. 39, last two displays: exterior pushforward
    and pullback are bounded by the m-th power of the original operator norm
    for mass and comass respectively. 9.39(2), pp. 87-88, gives the
    Euclidean exterior-power bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm ExteriorNormNaturality ExteriorMaps
  AlternatingCoordinates AlternatingPairing AlternatingDual LinearBasis
  AssociatedSubspace SimpleUnitBall OperatorNormUP ExteriorOperatorEstimate
  ComassUP ComassBounds MassUP MassOptimalDecomposition MassDecompositionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Maps.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variables (B : V -> V -> R) (C : U -> U -> R).
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> U}.
Variable L : R.
Hypothesis hL : is_operator_norm hB hC f L.
Variable m : nat.
Hypothesis hm : (0 < m)%N.

(** Source for [comass_pullback_bound]: Federer 1.8.1,
    p. 39, penultimate display. Evaluating on a simple unit vector
    reduces the assertion to the Euclidean exterior-map estimate.
    Only the source needs a finite basis once the norm laws are given. *)
Theorem comass_pullback_bound (phi : A_m U R^o m) a b :
  is_comass h2 hC phi a -> is_comass h2 hB (A_m_dual f phi) b ->
  b <= L^+m * a.
Proof.
move=> ha hb; apply: (@comass_least_upper_bound R h2 V B hB m
  (A_m_dual f phi) b hb (L^+m*a)) => x [hx hxn].
rewrite A_m_dual_pairing.
have hsimple := exterior_power_map_simple f hx.
have hpair := @comass_simple_bound R h2 U C hC m hm phi a ha
  (exterior_power_map f m x) hsimple.
apply: (le_trans (le_trans (ler_norm _) hpair)).
have hmap := @exterior_operator_pointwise_bound R h2 V U B C hB hC n e he f L hL m x.
have hunit : exterior_norm h2 hC (exterior_power_map f m x) <= L^+m.
  apply: (le_trans hmap).
  have hh := ler_wpM2l (exprn_ge0 m (operator_norm_nonnegative hL)) hxn.
  by rewrite mulr1 in hh.
have ha0 : 0 <= a := @comass_nonnegative R h2 U C hC m phi a hm ha.
exact: (ler_wpM2r ha0 hunit).
Qed.

(** Source for [mass_pushforward_bound]: Federer 1.8.1,
    p. 39, last display. Apply the Euclidean map estimate to the
    terms of an optimal simple decomposition and sum their lengths.
    The target may have arbitrary dimension when its comass laws exist. *)
Theorem mass_pushforward_bound (kV : A_m V R^o m -> R)
    (kU : A_m U R^o m -> R)
    (hkV : forall phi, is_comass h2 hB phi (kV phi))
    (hkU : forall phi, is_comass h2 hC phi (kU phi)) x a b :
  is_mass kV x a -> is_mass kU (exterior_power_map f m x) b -> b <= L^+m*a.
Proof.
move=> ha hb.
have [k [u [hkd [hu [hx hau]]]]] :=
  @mass_optimal_simple_decomposition R h2 V B hB n e he m hm kV hkV x a ha.
have hv i : simple (exterior_power_map f m (u i)) := exterior_power_map_simple f (hu i).
have hb' : is_mass kU (\sum_i exterior_power_map f m (u i)) b.
  by rewrite -linear_sum -hx.
have hh := @simple_decomposition_mass_bound R h2 U C hC m hm kU hkU
  (Finite.clone 'I_k _) (fun i => exterior_power_map f m (u i)) b hv hb'.
apply: (le_trans hh); rewrite hau mulr_sumr; apply: ler_sum => i _.
exact: (@exterior_operator_pointwise_bound R h2 V U B C hB hC n e he f L hL m (u i)).
Qed.
End Maps.
