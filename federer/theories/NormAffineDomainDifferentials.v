(** Federer (1969), 3.1.24, p. 239: supporting
    the scalar rational functions used to evaluate the
    analytic composition coefficient sum. This extends the
    affine precomposition law of 3.1.13 to actual open domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialChain NormDifferentialArithmetic NormClassOneUP NormClassOneLaws
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialFields
  NormAffineDilationDifferentials NormClassHigherUP NormClassHigherRestriction NormClassZeroComposition
  NormClassZeroArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section AffineDomains.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable A:X->Prop.
Hypothesis hA:forall x,A x -> norm_domain_interior NX A x.
Variable f:X->Y.
Variable c:R.
Variable b:X.
Local Notation T:=(fun x=>c*:x+b).
Local Notation B:=(fun x=>A (T x)).

(** Source for [norm_affine_preimage_interior]: supporting
    the rational scalar substitutions in Federer 3.1.24,
    p. 239. The inverse image of the actual open
    function domain under an affine scalar dilation is open. *)
Lemma norm_affine_preimage_interior x : B x -> norm_domain_interior NX B x.
Proof.
move=>hx.
have hcT:=norm_everywhere_differentiable_class_zero hNX
  (fun y (_:True)=>norm_affine_dilation_differential hNX c b y).
have [r [hr hb]]:=@hA (T x) hx.
have [d [hd hc]]:=(hcT x Logic.I).2 r hr.
exists d; split; first exact hd.
move=>v hv.
have hh:=hb (T (x+v)-T x) (hc v Logic.I hv).
by rewrite addrC subrK in hh.
Qed.

(** Source for [norm_higher_differential_affine_precomposition]:
    supporting the derivatives of cx/(1-cx) in Federer
    3.1.24, p. 239. For the actual inverse-image
    domain B, D^k(f(c*x+b))=c^k D^k f(c*x+b).
    This is proved from the first chain rule and the
    exact recursive differential laws; no extension across a
    pole or outside the function domain is used. *)
Theorem norm_higher_differential_affine_precomposition k (D:X->Z k) :
  (forall x,A x -> has_norm_higher_differential NX ev ZN A f k x (D x)) ->
  forall x,B x -> has_norm_higher_differential NX ev ZN B
    (fun y=>f (T y)) k x (c^+k*:D (T x)).
Proof.
elim:k D=>[D hD x hx|k ih D hD x hx].
- split; first exact hx.
  rewrite expr0 scale1r; exact (hD (T x) hx).2.
- have [P hP]:=norm_higher_differential_field_previous hNX hNY hZ hD.
  have hprev y (hy:B y):has_norm_higher_differential NX ev ZN B
      (fun t=>f (T t)) k y (c^+k*:P (T y)).
    exact (ih P hP y hy).
  have [L [hL he]]:=norm_higher_differential_field_step_elim hNX hP (hD (T x) hx).
  have hNk:=continuous_multilinear_norm_is_norm hNY (hZ k).
  have hchain:=norm_differential_chain hNX hNX hNk
    (norm_affine_dilation_differential hNX c b x) hL.
  have hrestrict:=norm_differential_restrict (fun y (hy:B y)=>conj Logic.I hy)
    (norm_affine_preimage_interior hx) hchain.
  have hscaled:=norm_differential_scale hNX hNk (c^+k) hrestrict.
  apply: (norm_higher_differential_field_step hNX hNY hZ hprev hscaled).
  move=>u v.
  rewrite hom_scaleE hom_compE hom_scaleE /= !linearZ.
  have :=he u v; rewrite /= => ->.
  by rewrite scalerA exprS mulrC.
Qed.

(** Source for [norm_class_infinity_affine_precomposition]:
    supporting the smooth scalar rational functions in Federer
    3.1.24, p. 239. Smoothness is preserved under
    affine substitution on the actual inverse-image domain.
    The proof uses the proved higher differential law and
    continuity of the scaled differential fields. *)
Theorem norm_class_infinity_affine_precomposition :
  norm_class_infinity NX NY ev ZN A f ->
  norm_class_infinity NX NY ev ZN B (fun x=>f (T x)).
Proof.
move=>hf.
have hcT:=norm_everywhere_differentiable_class_zero hNX
  (fun x (_:True)=>norm_affine_dilation_differential hNX c b x).
have hopen x (hx:B x):norm_domain_interior NX B x:=norm_affine_preimage_interior hx.
have hcomp (V:lmodType R) (NV:V->R) (g:X->V):
    norm_class_zero NX NV A g -> norm_class_zero NX NV B (fun x=>g (T x)).
  move=>hg.
  exact (norm_class_zero_open_restriction (fun x (hx:B x)=>conj Logic.I hx) hopen
    (norm_class_zero_composition hcT hg)).
move=>k; have [hc [D [hD hCD]]]:=hf k.
split; first exact (hcomp _ _ _ hc).
exists (fun x=>c^+k*:D (T x)); split.
- exact: norm_higher_differential_affine_precomposition hD.
- exact (norm_class_zero_scale (continuous_multilinear_norm_is_norm hNY (hZ k))
    (c^+k) (hcomp _ _ _ hCD)).
Qed.
End AffineDomains.
