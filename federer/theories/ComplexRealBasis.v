(** Federer (1969), 1.6.6, pp. 26-27: from a complex basis and its dual,
    obtain a real basis by pairing every vector with i times that vector.
    Its dual coordinates are the real and imaginary parts of the complex
    dual coordinates. Source context and the absence of this complex
    passage. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarUP
  ComplexScalarSealed ComplexScalarLaws Hom FiniteDualDimension
  FiniteBasisCriterion FiniteIndependence FiniteDimension LinearBasis Annihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section RealBasis.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation H := (ComplexScalars.laws R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation I := (Finite.clone ('I_n * bool)%type _).

(** Source for [realified_basis]: Federer 1.6.6, p. 26,
    displayed real basis e_1,i e_1,...,e_n,i e_n. False selects the
    original vector and true selects its imaginary multiple. *)
Definition realified_basis (j : I) : VR :=
  if j.2 then ii *: e j.1 else e j.1.

(** Source for [realified_coordinate]: Federer 1.6.6, p. 26,
    displayed real dual basis sigma_1,tau_1,...,sigma_n,tau_n.
    The corresponding real or imaginary part of the complex dual. *)
Definition realified_coordinate (j : I) (v : VR) : R :=
  if j.2 then ComplexScalars.im (dual_basis he j.1 v)
  else ComplexScalars.re (dual_basis he j.1 v).

(** Source for [realified_coordinate_linear]: Federer 1.6.6,
    p. 26, the displayed real dual basis. Supporting real linearity. *)
Lemma realified_coordinate_linear j : scalar (realified_coordinate j).
Proof.
case: j => j b; case: b; move=> a x y; rewrite /realified_coordinate /=.
- change (ComplexScalars.im (dual_basis he j (embed a *: x + y)) =
    a * ComplexScalars.im (dual_basis he j x) + ComplexScalars.im (dual_basis he j y)).
  rewrite linearP; exact: eq_trans (complex_im_add H _ _) (congr1 (fun z => z + _) (complex_im_scale H _ _)).
- change (ComplexScalars.re (dual_basis he j (embed a *: x + y)) =
    a * ComplexScalars.re (dual_basis he j x) + ComplexScalars.re (dual_basis he j y)).
  rewrite linearP; exact: eq_trans (complex_re_add H _ _) (congr1 (fun z => z + _) (complex_re_scale H _ _)).
Qed.
HB.instance Definition _ j := GRing.isLinear.Build R VR R^o *:%R
  (realified_coordinate j) (realified_coordinate_linear j).

(** Source for [realified_dual_imaginary]: Federer 1.6.6, p. 26,
    the displayed real dual basis. Supporting evaluation of a complex
    dual coordinate on an imaginary multiple of a basis vector. *)
Lemma realified_dual_imaginary i j :
  dual_basis he i (ii *: e j) = ii * dual_basis he i (e j).
Proof. exact: linearZ. Qed.

(** Source for [realified_coordinate_basis]: Federer 1.6.6,
    p. 26, the two displayed families are dual real bases.
    Supporting Kronecker-delta calculation. *)
Lemma realified_coordinate_basis i j :
  realified_coordinate i (realified_basis j) = if i == j then 1 else 0.
Proof.
case: i => i bi; case: j => j bj; case: bi; case: bj;
  rewrite xpair_eqE /= ?andbT ?andbF.
- change (ComplexScalars.im (dual_basis he i (ii *: e j)) = if i == j then 1 else 0).
  rewrite realified_dual_imaginary im_i_mul dual_basisE (eq_sym i j).
  by case: (j == i); rewrite ?(complex_re_one H) ?re_zero.
- change (ComplexScalars.im (dual_basis he i (e j)) = 0).
  rewrite dual_basisE.
  by case: (j == i); rewrite ?(complex_im_one H) ?im_zero.
- change (ComplexScalars.re (dual_basis he i (ii *: e j)) = 0).
  rewrite realified_dual_imaginary re_i_mul dual_basisE.
  by case: (j == i); rewrite ?(complex_im_one H) ?im_zero oppr0.
- change (ComplexScalars.re (dual_basis he i (e j)) = if i == j then 1 else 0).
  rewrite dual_basisE (eq_sym i j).
  by case: (j == i); rewrite ?(complex_re_one H) ?re_zero.
Qed.

(** Source for [realified_basis_expansion]: Federer 1.6.6,
    p. 26, the displayed real bases. Every vector is reconstructed from
    the real and imaginary parts of its complex coordinates. *)
Lemma realified_basis_expansion (v : VR) :
  v = \sum_j (realified_coordinate j v) *: realified_basis j.
Proof.
rewrite /realified_coordinate /realified_basis.
rewrite -(pair_bigA +%R (fun (j : 'I_n) (b : bool) =>
  @GRing.scale R VR
    (if b then ComplexScalars.im (dual_basis he j v) else ComplexScalars.re (dual_basis he j v))
    (if b then ii *: e j else e j))).
under eq_bigr do rewrite big_bool.
rewrite [v in LHS](basis_vector_expansion he v).
apply: eq_bigr => j _.
change ((dual_basis he j v : C) *: e j =
  embed (ComplexScalars.im (dual_basis he j v)) *: (ii *: e j) +
  embed (ComplexScalars.re (dual_basis he j v)) *: e j).
rewrite scalerA -scalerDl [embed _ * ii]mulrC addrC.
by rewrite -(complex_decomposition H).
Qed.

(** Source for [realified_basisP]: Federer 1.6.6, p. 26,
    the displayed real basis. The family is both independent and spanning,
    including the zero-dimensional case. *)
Theorem realified_basisP : is_basis realified_basis.
Proof.
apply: finite_basis_criterion.
- apply: (@finite_independent_separating R I VR realified_basis
    (fun j => GRing.Linear.clone R VR R^o *:%R (realified_coordinate j) _)).
  exact: realified_coordinate_basis.
- move=> v; exists (fun j => realified_coordinate j v).
  exact: realified_basis_expansion.
Qed.
(** Source for [realified_covector]: Federer 1.6.6, p. 26,
    the displayed real dual basis. Real and imaginary coordinates
    packaged as real linear functionals. *)
Definition realified_covector j : Hom VR R^o :=
  hom_of_linear (GRing.Linear.clone R VR R^o *:%R (realified_coordinate j) _).

(** Source for [realified_covector_dual]: Federer 1.6.6,
    p. 26, the displayed dual real bases. Identification of the named
    coordinate functional with the unique dual basis functional. *)
Lemma realified_covector_dual j : realified_covector j = dual_basis realified_basisP j.
Proof.
apply: hom_ext => v.
apply: (basis_linear_ext realified_basisP
  (hom_as_linear (realified_covector j))
  (hom_as_linear (dual_basis realified_basisP j))) v => k.
change (realified_coordinate j (realified_basis k) = dual_basis realified_basisP j (realified_basis k)).
by rewrite realified_coordinate_basis dual_basisE eq_sym.
Qed.

(** Source for [realified_covector_basisP]: Federer 1.6.6,
    p. 26, the displayed real dual basis. The coordinate functionals
    themselves form a basis of the entire real dual. *)
Theorem realified_covector_basisP : is_basis realified_covector.
Proof.
apply: (basis_congr (fun j => esym (realified_covector_dual j))).
exact: dual_basisP.
Qed.

(** Source for [realified_finite_space]: Federer 1.6.6,
    pp. 26-27, real dimension twice the complex dimension, implicit
    in the displayed paired basis. Supporting finite-space interface. *)
Definition realified_finite_space : vectType R := finite_basis_vect realified_basisP.

(** Source for [realified_dimension]: Federer 1.6.6,
    pp. 26-27, displayed paired real basis and even-dimensional
    complex planes. The underlying real dimension is twice n. *)
Theorem realified_dimension : dim realified_finite_space = (n * 2)%N.
Proof. by rewrite finite_basis_dimension card_prod card_ord card_bool. Qed.
End RealBasis.
