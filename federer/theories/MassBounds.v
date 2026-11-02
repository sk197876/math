(** Federer (1969), 1.8.1, p. 38: elementary consequences of the dual
    definition of mass. These consequences use only the abstract comass and
    mass laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading
  AlternatingCoordinates AlternatingPairing AssociatedSubspace
  ComassUP ComassBounds ComassHomogeneity MassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
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

(** Source for [comass_function_zero]: Federer 1.8.1, p. 38,
    supporting zero law for any function satisfying the comass specification. *)
Lemma comass_function_zero : kappa 0 = 0.
Proof. exact: comass_unique (hk 0) (comass_zero h2 hB hm). Qed.

(** Source for [comass_function_opp]: Federer 1.8.1, p. 38,
    supporting symmetry of the comass unit ball used in mass estimates. *)
Lemma comass_function_opp phi : kappa (-phi) = kappa phi.
Proof.
have hh := @comass_absolute_homogeneity R h2 V B hB m hm phi (-1)
  (kappa phi) (kappa (-1 *: phi)) (hk phi) (hk (-1 *: phi)).
by rewrite scaleN1r normrN normr1 mul1r in hh.
Qed.

(** Source for [mass_nonnegative]: Federer 1.8.1, p. 38,
    supporting nonnegativity: the zero covector belongs to the comass ball. *)
Lemma mass_nonnegative x d : is_mass kappa x d -> 0 <= d.
Proof.
move=> hd; have hk0 : kappa 0 <= 1 by rewrite comass_function_zero.
have hh := @mass_upper_law R V m kappa x d hd 0 hk0.
by rewrite (bil0r P) in hh.
Qed.

(** Source for [mass_zero]: Federer 1.8.1, p. 38,
    supporting zero law for the mass supremum. *)
Lemma mass_zero : is_mass kappa (0 : exterior_power V m) 0.
Proof.
constructor.
- move=> phi hphi; by rewrite (bil0l P).
- move=> eps heps; exists 0; split; first by rewrite comass_function_zero.
  by rewrite (bil0l P) sub0r oppr_lt0.
Qed.

(** Source for [mass_absolute_unit_bound]: Federer 1.8.1,
    p. 38, supporting absolute pairing bound on the comass ball. *)
Lemma mass_absolute_unit_bound x d (hd : is_mass kappa x d) phi :
  kappa phi <= 1 -> `|pairing x phi| <= d.
Proof.
move=> hphi; rewrite ler_norml; apply/andP; split.
- have hn : kappa (-phi) <= 1 by rewrite comass_function_opp.
  have hh := @mass_upper_law R V m kappa x d hd (-phi) hn.
  rewrite -scaleN1r (bilZr P) scaleN1r in hh.
  by rewrite lerNl.
- exact (@mass_upper_law R V m kappa x d hd phi hphi).
Qed.

(** Source for [mass_triangle]: Federer 1.8.1, p. 38,
    supporting triangle inequality for the dual supremum norm. *)
Theorem mass_triangle x y d e f :
  is_mass kappa x d -> is_mass kappa y e -> is_mass kappa (x+y) f -> f <= d+e.
Proof.
move=> hd he hf; apply: (@mass_least_upper_bound R V m kappa (x+y) f hf (d+e)) => phi hphi.
rewrite (bilDl P).
exact: lerD (@mass_upper_law R V m kappa x d hd phi hphi)
  (@mass_upper_law R V m kappa y e he phi hphi).
Qed.

(** Source for [simple_mass_upper]: Federer 1.8.1, p. 38, supporting
    simple-vector half of the equality criterion: mass is at most Euclidean
    norm on simple vectors. The reverse norm inequality will give equality. *)
Theorem simple_mass_upper x d : simple x -> is_mass kappa x d ->
  d <= exterior_norm h2 hB x.
Proof.
move=> hx hd; apply: (@mass_least_upper_bound R V m kappa x d hd (exterior_norm h2 hB x)) => phi hphi.
have hh := le_trans (ler_norm (pairing x phi))
  (@comass_simple_bound R h2 V B hB m hm phi (kappa phi) (hk phi) x hx).
apply: (le_trans hh).
have ht := ler_wpM2l (exterior_norm_nonnegative h2 hB x) hphi.
by rewrite mulr1 in ht.
Qed.
End Bounds.
