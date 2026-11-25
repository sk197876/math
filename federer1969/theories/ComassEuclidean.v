(** Federer (1969), 1.8.1, p. 38: comparison of comass with the induced
    Euclidean norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerExterior InnerExteriorPositivity InnerExteriorIsomorphism InnerExteriorBasis
  ExteriorNorm ExteriorCovectorInner ExteriorPairingBound
  SimpleUnitBall ComassUP ComassBounds SimpleAdaptedBasis
  OrthonormalFamilies OrthonormalParseval GramSchmidt OrthonormalisationUP
  ExteriorGrading ExteriorIndices FiniteExteriorPowers AlternatingCoordinates
  AlternatingPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Comparison.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Local Notation D := (@exterior_covector_norm R h2 V B hB n e he m).

(** Source for [comass_le_euclidean]: Federer 1.8.1,
    p. 38, first inequality: the comass is at most the Euclidean
    norm of the covector. This follows from the Cauchy pairing bound. *)
Theorem comass_le_euclidean (phi : A_m V R^o m) c :
  is_comass h2 hB phi c -> c <= D phi.
Proof.
move=> hc; apply: (@comass_least_upper_bound R h2 V B hB m phi c hc (D phi)) => x [hs hx].
have hh := le_trans (ler_norm (pairing x phi))
  (@exterior_pairing_bound R h2 V B hB n e he m x phi).
apply: (le_trans hh).
have hn : 0 <= D phi := inner_norm_nonnegative _ _.
have ht := ler_wpM2r hn hx; by rewrite mul1r in ht.
Qed.

(** Source for [covector_orthonormal_parseval]: Federer 1.8.1, p. 38,
    supporting coordinate square identity for the lower bound *)
Lemma covector_orthonormal_parseval (d : 'I_n -> V) (hd : is_basis d)
    (ho : orthonormal_family B d) (phi : A_m V R^o m) :
  (D phi)^+2 = \sum_(lambda : Lambda n m) (pairing (e_lambda d (val lambda)) phi)^+2.
Proof.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
rewrite -(hgf phi) inner_exterior_form_norm exterior_norm_square.
rewrite (@orthonormal_parseval R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m) (@exterior_inner_productP R h2 V B hB m)
  (Finite.clone (Lambda n m) _) (fun lambda => e_lambda d (val lambda))
  (@exterior_orthonormal_family R h2 V B hB n d ho m)
  (@finite_e_lambda_basis R n V d hd h2 m)).
apply: eq_bigr => lambda _.
by rewrite (inner_symmetric (@exterior_inner_productP R h2 V B hB m)).
Qed.

(** Source for [euclidean_squared_le_comass]: Federer 1.8.1, p. 38, squared
    form of the binomial norm comparison, valid also when the exterior power
    has dimension zero. *)
Theorem euclidean_squared_le_comass (phi : A_m V R^o m) c :
  (0 < m)%N -> is_comass h2 hB phi c -> (D phi)^+2 <= ('C(n,m))%:R * c^+2.
Proof.
move=> hm hc; have [d [hd hdo]] := orthonormal_basis_exists hB he.
have ho := orthonormalisation_orthonormal hdo.
rewrite (covector_orthonormal_parseval hd ho).
have hsum : (\sum_(lambda : Lambda n m) (pairing (e_lambda d (val lambda)) phi)^+2)
    <= \sum_(lambda : Lambda n m) c^+2.
  apply: ler_sum => lambda _.
  have hn : exterior_norm h2 hB (e_lambda d (val lambda)) = 1.
    exact: (@orthonormal_norm1 R (exterior_power V m)
      (@exterior_inner_form R h2 V B hB m) (@exterior_inner_productP R h2 V B hB m)
      (Finite.clone (Lambda n m) _) (fun l => e_lambda d (val l))
      (@exterior_orthonormal_family R h2 V B hB n d ho m) lambda).
  have hs : simple_unit_ball h2 hB (e_lambda d (val lambda)).
    split; first exact: indexed_product_simple.
    by rewrite hn.
  have hb := @comass_absolute_unit_bound R h2 V B hB m hm phi c hc _ hs.
  have hc0 : 0 <= c := comass_nonnegative hm hc.
  have hsq : `|pairing (e_lambda d (val lambda)) phi|^+2 <= c^+2.
    by rewrite (ler_sqr (normr_ge0 _) hc0).
  by rewrite -normrX ger0_norm ?sqr_ge0 in hsq.
rewrite sumr_const card_Lambda -mulr_natl in hsum.
exact hsum.
Qed.
End Comparison.
