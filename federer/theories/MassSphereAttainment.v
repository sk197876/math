(** Federer (1969), 1.8.4, p. 41: unit-comass
    attainment also for zero multivectors when the exterior space
    is nonzero. The condition m<=dim V supplies a unit simple
    covector; without it the closed-ball statement is the valid one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SimpleAdaptedBasis InnerProductUP
  InnerNorm InnerNormalization InitialIndices InnerExterior InnerExteriorPositivity InnerExteriorBasis ExteriorNorm
  ExteriorCovectorInner ExteriorGrading ExteriorIndices FiniteExteriorPowers
  OrthonormalFamilies OrthonormalisationUP GramSchmidt LinearBasis
  AlternatingCoordinates AlternatingPairing ComassUP ComassSimpleEquality
  MassUP MassBounds MassEuclidean MassUnitAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Attainment.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Hypothesis hmn : (m <= n)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).

(** Source for [unit_comass_covector_exists]: Federer 1.8.4,
    p. 41, supporting existence of a unit covector even when the
    multivector to be evaluated is zero, provided m<=dim V. *)
Theorem unit_comass_covector_exists : exists phi, kappa phi = 1.
Proof.
have [f [hf hfo]] := orthonormal_basis_exists hB he.
have ho := orthonormalisation_orthonormal hfo.
pose u := e_lambda f (val (Lambda_initial hmn)).
have hu : exterior_norm h2 hB u = 1.
  exact: (@orthonormal_norm1 R (exterior_power V m)
    (@exterior_inner_form R h2 V B hB m) (@exterior_inner_productP R h2 V B hB m)
    (Finite.clone (Lambda n m) _) (fun l => e_lambda f (val l))
    (@exterior_orthonormal_family R h2 V B hB n f ho m) (Lambda_initial hmn)).
pose phi := inner_exterior_form h2 hB u.
have hs := inner_exterior_simple h2 hB (indexed_product_simple f (val (Lambda_initial hmn))).
have hh := @simple_comass_euclidean R h2 V B hB n e he m hm phi (kappa phi) hs (hk phi).
exists phi; by rewrite /phi inner_exterior_form_norm hu in hh.
Qed.

(** Source for [mass_attained_on_comass_sphere]: Federer 1.8.4,
    p. 41, the printed unit-comass maximizer for every multivector
    when the exterior degree does not exceed dim V. The zero
    multivector is included under this explicit dimension condition. *)
Theorem mass_attained_on_comass_sphere (x : exterior_power V m) d
    (hd : is_mass kappa x d) : exists phi, kappa phi = 1 /\ pairing x phi=d.
Proof.
case hx : (x == 0).
- move/eqP: hx=> hz.
  have hd0 : d=0.
    apply: mass_unique (@mass_zero R h2 V B hB m hm kappa hk).
    by rewrite -hz.
  have [phi hp] := unit_comass_covector_exists.
  exists phi; split=> //.
  by rewrite hz hd0 (bil0l (@pairing_bilinear R V R^o m)).
- have hNx : 0 < exterior_norm h2 hB x.
    by rewrite lt_def exterior_norm_eq0 hx exterior_norm_nonnegative.
  have hNd := @euclidean_le_mass R h2 V B hB n e he m hm kappa hk x d hd.
  exact: (@positive_mass_attained_on_comass_sphere R h2 V B hB n e he m hm
    kappa hk x d hd (lt_le_trans hNx hNd)).
Qed.
End Attainment.
