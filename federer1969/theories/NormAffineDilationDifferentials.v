(** Federer (1969), 3.1.13, p. 224:
    differentiating a translated scalar dilation
    multiplies the ith differential by c^i.
    This gives the exact scaling of the
    radial cutoff derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormClassOneUP NormDifferentialLocal
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain NormClassOneLaws
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialFields NormClassHigherUP
  NormClassZeroArithmetic NormClassZeroComposition NormClassHigherRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_affine_dilation_differential]:
    the differential of x |-> c*x+b
    is c times identity, supporting the
    bump rescaling in Federer 3.1.13,
    p. 224. Scalar zero is included. *)
Lemma norm_affine_dilation_differential (R : realType)
    (X : lmodType R) (N : X->R) (hN : is_real_norm N)
    (c : R) (b a : X) :
  has_norm_differential N N (fun _=>True) (fun x=>c*:x+b) a
    (c*:hom_of_linear (linear_id X)).
Proof.
split.
- exists 1; split; first exact: ltr01; by move=>v hv.
- exists `|c|; split; first exact: normr_ge0.
  by move=>v; rewrite hom_scaleE /= (real_seminorm_scale hN.1).
- move=>e he; exists 1; split; first exact: ltr01.
  move=>v _ hv; rewrite hom_scaleE /=.
  have ht : c*:(a+v)+b=(c*:a+b)+c*:v by rewrite scalerDr addrAC.
  rewrite ht addrAC addrK subrr (real_seminorm_zero hN.1).
  exact: (mulr_ge0 (ltW he) (real_seminorm_nonnegative hN.1 v)).
Qed.

Section HigherDilation.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable f : X->Y.
Variable c : R.
Variable b : X.
Local Notation T := (fun x=>c*:x+b).

(** Source for [norm_higher_differential_affine_dilation]:
    D^i(f(c*x+b))=c^i D^i f(c*x+b),
    supporting the displayed bump-derivative formula
    in Federer 3.1.13, p. 224.
    Only the actual derivative field of
    the indicated order is assumed. *)
Theorem norm_higher_differential_affine_dilation k (D : X->Z k) :
  (forall x, has_norm_higher_differential NX ev ZN (fun _=>True) f k x (D x)) ->
  forall x, has_norm_higher_differential NX ev ZN (fun _=>True)
    (fun y=>f (T y)) k x (c^+k*:D (T x)).
Proof.
elim:k D=>[D hD x|k ih D hD x].
- split; first exact I; by rewrite expr0 scale1r; exact: (hD (T x)).2.
- have hfield x (_ : True) := hD x.
  have [P hP] := norm_higher_differential_field_previous hNX hNY hZ hfield.
  have hprev y : has_norm_higher_differential NX ev ZN (fun _=>True)
      (fun t=>f (T t)) k y (c^+k*:P (T y)).
    apply: ih=>t; exact: (hP t I).
  have [L [hL he]] := norm_higher_differential_field_step_elim hNX hP (hD (T x)).
  have hNk := continuous_multilinear_norm_is_norm hNY (@hZ k).
  have hchain := norm_differential_chain hNX hNX hNk
    (norm_affine_dilation_differential hNX c b x) hL.
  have hopen : norm_domain_interior NX (fun _=>True) x.
    exists 1; split; first exact: ltr01; by move=>v hv.
  have hrestrict := norm_differential_restrict (fun _ (_ : True)=>conj I I) hopen hchain.
  have hscaled := norm_differential_scale hNX hNk (c^+k) hrestrict.
  apply: (norm_higher_differential_field_step hNX hNY hZ
    (fun y (_ : True)=>hprev y) hscaled).
  move=>u v.
  rewrite hom_scaleE hom_compE hom_scaleE /= !linearZ.
  have := he u v; rewrite /= => ->.
  by rewrite scalerA exprS mulrC.
Qed.

(** Source for [norm_class_infinity_affine_dilation]:
    translating and scaling the argument preserves
    every differentiability class, supporting the
    smooth bumps in Federer 3.1.13,
    p. 224. *)
Theorem norm_class_infinity_affine_dilation :
  norm_class_infinity NX NY ev ZN (fun _=>True) f ->
  norm_class_infinity NX NY ev ZN (fun _=>True) (fun x=>f (T x)).
Proof.
move=>hf.
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hcT := norm_everywhere_differentiable_class_zero hNX
  (fun x (_ : True)=>norm_affine_dilation_differential hNX c b x).
have hrestrict (V : lmodType R) (NV : V->R) (g : X->V) :
    norm_class_zero NX NV (fun _=>True) g ->
    norm_class_zero NX NV (fun _=>True) (fun x=>g (T x)).
  move=>hg; exact: norm_class_zero_open_restriction
    (fun _ (_ : True)=>conj I I) hopen (norm_class_zero_composition hcT hg).
move=>k; have [hc [D [hD hDc]]] := hf k.
split; first by have hh := hrestrict _ _ _ hc.
exists (fun x=>c^+k*:D (T x)); split.
- move=>x _; apply: norm_higher_differential_affine_dilation=>y; exact: (hD y I).
- have hh := norm_class_zero_scale
    (continuous_multilinear_norm_is_norm hNY (@hZ k)) (c^+k) (hrestrict _ _ _ hDc).
  exact hh.
Qed.
End HigherDilation.
