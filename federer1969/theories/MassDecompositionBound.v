(** Federer (1969), 1.8.1, pp. 38-39: the mass is no greater than the sum of
    the lengths in any simple decomposition. Here the claim follows directly
    from the dual supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading
  AlternatingCoordinates AlternatingPairing AssociatedSubspace SimpleElementary
  SimpleUnitBall ComassUP ComassBounds MassUP SubconvexCombinations Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bound.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).
Local Notation P := (@pairing_bilinear R V R^o m).
Local Notation N := (@exterior_norm R h2 V B hB m).

(** Source for [simple_decomposition_mass_bound]: Federer
    1.8.1, pp. 38-39, lower-bound half of the printed infimum
    formula: every finite simple decomposition has total length at
    least the mass. The index set may be empty. *)
Theorem simple_decomposition_mass_bound (I : finType)
    (u : I -> exterior_power V m) d :
  (forall i, simple (u i)) -> is_mass kappa (\sum_i u i) d -> d <= \sum_i N (u i).
Proof.
move=> hu hd; apply: (@mass_least_upper_bound R V m kappa (\sum_i u i) d hd
  (\sum_i N (u i))) => phi hphi.
rewrite (big_morph (fun x => pairing x phi) (fun x y => bilDl P x y phi) (bil0l P phi)).
apply: ler_sum => i _.
have hh := le_trans (ler_norm (pairing (u i) phi))
  (@comass_simple_bound R h2 V B hB m hm phi (kappa phi) (hk phi) (u i) (hu i)).
apply: (le_trans hh).
have ht := ler_wpM2l (exterior_norm_nonnegative h2 hB (u i)) hphi.
by rewrite mulr1 in ht.
Qed.

(** Source for [subconvex_mass_bound]: Federer 1.8.1,
    p. 38, inclusion of the convex hull of S in the mass unit
    ball. Nonnegative coefficients of total at most one are allowed
    because zero belongs to S in positive degree. *)
Theorem subconvex_mass_bound x d :
  subconvex_combinations (@simple_unit_ball R h2 V B hB m) x ->
  is_mass kappa x d -> d <= 1.
Proof.
move=> [n [u [a [hu [ha [hs hx]]]]]] hd.
rewrite hx in hd.
have hsimple i : simple (a i *: u i) := simple_scale (a i) hm (proj1 (hu i)).
have hh := @simple_decomposition_mass_bound (Finite.clone 'I_n _)
  (fun i => a i *: u i) d hsimple hd.
apply: (le_trans hh); apply: (le_trans _ hs).
apply: ler_sum => i _; rewrite exterior_norm_scale (ger0_norm (ha i)).
have ht := ler_wpM2l (ha i) (proj2 (hu i)); by rewrite mulr1 in ht.
Qed.
End Bound.
