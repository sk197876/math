(** Federer (1969), 3.1.11, p. 220:
    differentiation of a polynomial obtained by evaluating
    a continuous multilinear map repeatedly at the same
    vector. The argument uses 3.1.1(2),(4), p. 210,
    through the opaque finite-product interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  NormedFamilyUP NormedFamilyLaws NormedFamilySealed NormedFamilyLinearAssembly
  NormDifferentialUP NormDifferentialLinear NormDifferentialChain
  NormDifferentialLocal NormDifferentialMultilinear
  ContinuousMultilinearUP NormBoundedMultilinearContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_diagonal_multilinear_differential]:
    supporting first derivative of the polynomial in
    Federer 3.1.11, p. 220. The derivative
    is the sum of the single-argument replacements.
    No symmetry, finite dimension or completeness is assumed. *)
Theorem norm_diagonal_multilinear_differential (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (f : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  forall a, exists L : Hom X Y,
    has_norm_differential NX NY (fun _=>True)
      (fun x=>f [ffun _ : 'I_k=>x]) a L /\
    forall v, L v=\sum_(i<k) f (family_with (i:=i) [ffun _ : 'I_k=>a] v).
Proof.
move=> hf a.
pose V := fun _ : 'I_k=>X.
pose N := fun _ : 'I_k=>NX.
pose P := @NormedFamily.space R k V.
pose coordinate := @NormedFamily.coordinate R k V.
pose PN := @NormedFamily.norm R k V N.
have hP : is_normed_family N coordinate PN := @NormedFamily.laws R k V N.
have hPN := @normed_family_is_norm R k V N (fun _=>hNX) P coordinate PN hP.
have [D [hD [hDN hDb]]] := normed_family_diagonal_exists hP.
have hcont := norm_bounded_multilinear_continuous hNX hNY hP hf.
have [M [hM hMe]] := @norm_differential_multilinear R k V Y P N NY
  (fun _=>hNX) hNY coordinate PN hP f hf.1 hcont (D a).
have hInt : norm_domain_interior NX (fun _ : X=>True) a.
  exists 1; split; first exact: ltr01; by move=> h hh.
have hdiag := @norm_differential_linear R X P NX PN hNX hPN
  (fun _=>True) a D hInt hDb.
have hcomp := norm_differential_chain hNX hPN hNY hdiag hM.
have hre := norm_differential_restrict
  (fun (x : X) (_ : True)=>conj Logic.I Logic.I) hInt hcomp.
have he x : [ffun i : 'I_k=>coordinate i (D x)]=[ffun _ : 'I_k=>x].
  by apply/ffunP=> i; rewrite !ffunE hD.
exists (hom_comp M D); split.
- apply: (@norm_differential_domain_agreement R X Y NX NY hNX
    (fun _=>True) (fun x=>f [ffun i : 'I_k=>coordinate i (D x)])
    (fun x=>f [ffun _ : 'I_k=>x]) a (hom_comp M D) _ hre).
  by move=> x _; rewrite he.
- move=> v; rewrite hom_compE hMe he.
  apply: eq_bigr=> i _; by rewrite hD.
Qed.

(** Source for [norm_diagonal_multilinear_differential_candidate]:
    the derivative formula for diagonal polynomials in
    Federer 3.1.11, p. 220, with a prescribed
    linear map. Its continuity follows from the proved
    multilinear derivative rather than an extra hypothesis. *)
Theorem norm_diagonal_multilinear_differential_candidate (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (f : {ffun 'I_k->X}->Y) (a : X) (L : Hom X Y) :
  norm_bounded_multilinear NX NY f ->
  (forall v, L v=\sum_(i<k) f (family_with (i:=i) [ffun _ : 'I_k=>a] v)) ->
  has_norm_differential NX NY (fun _=>True)
    (fun x=>f [ffun _ : 'I_k=>x]) a L.
Proof.
move=> hf hL.
have [M [hM hMe]] := norm_diagonal_multilinear_differential hNX hNY hf a.
have he : M=L by apply: hom_ext=> v; rewrite hMe hL.
by rewrite -he.
Qed.
