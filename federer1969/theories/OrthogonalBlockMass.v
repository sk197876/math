(** Federer (1969), 1.8.4, pp. 40-41: the mass of an orthonormal block
    wedged with a multivector supported in an orthogonal subspace is the
    mass of that multivector. The proof uses the displayed annihilating
    covectors and a mass-attaining covector, followed by the sharp
    simple-factor comass bound. Source context and the attainment boundary:
    MassAttainment.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SimpleCovectors InnerProductUP InnerPolarity
  InnerExterior InnerExteriorProducts ExteriorCovectorInner ExteriorNorm
  OrthonormalFamilies ExteriorMaps ExteriorHomogeneousProducts
  AlternatingCoordinates AlternatingPairing AlternatingProduct CovectorProducts
  ComassUP ComassSimpleEquality ComassSimpleWedgeBound
  MassUP MassSealed MassEquality MassWedgeBound MassAttainment
  AnnihilatingBlockPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Block.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables U V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variables p q : nat.
Hypotheses (hp : (0 < p)%N) (hq : (0 < q)%N).
Variable kp : A_m V R^o p -> R.
Variable kq : A_m V R^o q -> R.
Variable kr : A_m V R^o (p+q) -> R.
Hypothesis hkp : forall phi, is_comass h2 hB phi (kp phi).
Hypothesis hkq : forall phi, is_comass h2 hB phi (kq phi).
Hypothesis hkr : forall phi, is_comass h2 hB phi (kr phi).
Variable e : 'I_p -> V.
Hypothesis ho : orthonormal_family B e.
Variable f : {linear U -> V}.
Hypothesis hf : forall i u, B (e i) (f u) = 0.
Local Notation volume := (e_lambda e (ord_tuple p)).
Local Notation alpha := (inner_exterior_form h2 hB volume).

(** Source for [orthonormal_block_polar_comass]: Federer 1.8.4,
    p. 40, the product of the orthonormal annihilating covectors
    has comass one. It is the polarity image of the unit volume. *)
Lemma orthonormal_block_polar_comass : kp alpha = 1.
Proof.
have hs : simple_covector h2 alpha := inner_exterior_simple h2 hB (product_simple e).
have hh := @simple_comass_euclidean R h2 V B hB n b hb p hp alpha (kp alpha) hs (hkp alpha).
by rewrite inner_exterior_form_norm (orthonormal_product_unit_norm h2 hB ho) in hh.
Qed.

(** Source for [orthonormal_block_pairing]: Federer 1.8.4,
    p. 41, the displayed product pairing, normalized so the
    first block and its polarity image pair to one. *)
Lemma orthonormal_block_pairing (y : exterior_power U q) (psi : A_m V R^o q) :
  pairing (exterior_product volume (exterior_power_map f q y))
    (form_wedge h2 (scalar_bilinear R) alpha psi) =
  pairing (exterior_power_map f q y) psi.
Proof.
rewrite inner_exterior_product_covectors.
apply: annihilating_block_pairing.
- move=> i j; by rewrite one_homE inner_polarityE ho eq_sym.
- move=> i u; by rewrite one_homE inner_polarityE (inner_symmetric hB) hf.
Qed.

(** Source for [orthonormal_block_mass]: Federer 1.8.4,
    pp. 40-41, the orthonormal first-factor case of mass
    multiplicativity on mutually orthogonal subspaces. The second
    factor is unrestricted, including zero and nonsimple vectors. *)
Theorem orthonormal_block_mass (y : exterior_power U q) d c
    (hd : is_mass kq (exterior_power_map f q y) d)
    (hc : is_mass kr (exterior_product volume (exterior_power_map f q y)) c) : c=d.
Proof.
have [psi [hpsi hpair]] := @mass_attained R h2 V B hB n b hb q hq kq hkq
  (exterior_power_map f q y) d hd.
have hs : simple_covector h2 alpha := inner_exterior_simple h2 hB (product_simple e).
have hw := @comass_simple_left_wedge_bound R h2 V B hB n b hb p q hp hq
  alpha psi (kp alpha) (kq psi) (kr (form_wedge h2 (scalar_bilinear R) alpha psi))
  hs (hkp alpha) (hkq psi) (hkr _).
rewrite orthonormal_block_polar_comass mul1r in hw.
have hl := @mass_upper_law R V (p+q) kr _ c hc
  (form_wedge h2 (scalar_bilinear R) alpha psi) (le_trans hw hpsi).
rewrite orthonormal_block_pairing hpair in hl.
pose a := @MassSealed.Mass.norm R h2 V B hB n b hb p hp kp hkp volume.
have ha : is_mass kp volume a := @MassSealed.Mass.laws R h2 V B hB n b hb p hp kp hkp volume.
have ha1 : a = 1.
  rewrite (@simple_mass_euclidean R h2 V B hB n b hb p hp kp hkp volume a (product_simple e) ha).
  exact (@orthonormal_product_unit_norm R h2 V B hB p e ho).
have hu := @mass_wedge_bound R h2 V B hB n b hb p q hp hq kp kq kr hkp hkq hkr
  volume (exterior_power_map f q y) a d c ha hd hc.
rewrite ha1 mul1r in hu.
apply/eqP; rewrite eq_le; exact/andP.
Qed.
End Block.
