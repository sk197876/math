(** Federer (1969), 3.2.28(4), printed p. 266:
    the actual differential of T(x)=x^2/2 is h to hx.
    The proved homogeneous polynomial differential theorem
    identifies it with the Chapter 1 symmetric contraction;
    the coefficient is never assumed to be a derivative. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  SymmetricGrading SymmetricForms SymmetricFormIsomorphism InnerSymmetricPositivity
  HomogeneousPolynomialFunctions PolynomialTaylorTerms PolynomialTaylorTermContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst HomogeneousPolynomialDifferentials
  NormDifferentialUP NormDifferentialLocal NormOpenDomainLaws SymmetricSquareGeometry SymmetricSquareSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Differential.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation Y:=(symmetric_power V 2).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation NY:=(inner_norm hS).
Local Notation hNY:=(inner_norm_real_norm hS).
Local Notation phi:=(@symmetric_square_coefficient R V).

(** Source for [inner_projective_square_differential_exists]:
    DT(x)h=hx, the displayed formula in Federer
    3.2.28(4), p. 266. The two factors are in
    the symmetric algebra, so their order is immaterial.
    This proves actual differentiability, also at zero. *)
Theorem inner_projective_square_differential_exists (x:V):
  exists L:Hom V Y,
    has_norm_differential NX NY (fun _=>True) (@inner_projective_square R V) x L /\
    forall h,L h=symmetric_tuple_component [tuple h;x].
Proof.
pose Z j:=@ContinuousMultilinear.space R j V Y NX NY hNX hNY.
pose ev j:=@ContinuousMultilinear.evaluation R j V Y NX NY hNX hNY.
pose ZN j:=@ContinuousMultilinear.norm R j V Y NX NY hNX hNY.
have hZ j:is_continuous_multilinear_space NX NY (ev j) (ZN j):=
  @ContinuousMultilinear.laws R j V Y NX NY hNX hNY.
have [D [hDe [hD hCont]]]:=@homogeneous_polynomial_differential_fields R V Y NX NY
  hNX hNY Z ev ZN hZ (fun _=>True)
  (fun a _=>@norm_full_domain_interior R V NX a) 2 phi
  (@symmetric_square_coefficient_bounded R V B hB).
pose L:=@continuous_multilinear_one_operator R V Y (Z 1%N) NX NY
  (ev 1%N) (ZN 1%N) (hZ 1%N) (D 1%N x).
have hd:has_norm_differential NX NY (fun _=>True) (sform_polynomial_value phi) x L.
  exact:(@norm_higher_differential_first R V Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) (sform_polynomial_value phi) x (D 1%N x)).1
    (hD 1%N x Logic.I).
exists L; split.
- apply:(@norm_differential_domain_agreement R V Y NX NY hNX (fun _=>True)
    (sform_polynomial_value phi) (@inner_projective_square R V) x L _ hd).
  move=>a _; exact:symmetric_square_polynomial_value.
- move=>h.
  change (ev 1%N [ffun _:'I_1=>h] (D 1%N x)=symmetric_tuple_component [tuple h;x]).
  rewrite hDe (@symmetric_taylor_term_tuple_value R V Y 2 1 (isT: (1<=2)%N)
    phi x [tuple [ffun _:'I_1=>h] j|j<1]) /symmetric_square_coefficient
    hom_to_sformE hom_of_linearE /=.
  rewrite invr1 scale1r.
  have hTuple:tcast (subnKC (isT:(1<=2)%N))
      [tuple of [tuple [ffun _: 'I_1=>h] j|j<1]++[tuple x|j<1]]=[tuple h;x].
    apply:val_inj.
    change (tval (tcast (subnKC (isT:(1<=2)%N))
      [tuple of [tuple [ffun _: 'I_1=>h] j|j<1]++[tuple x|j<1]])=[::h;x]).
    by rewrite val_tcast /= enum_ordSl enum_ord0 /= ffunE.
  by rewrite hTuple.
Qed.
End Differential.
