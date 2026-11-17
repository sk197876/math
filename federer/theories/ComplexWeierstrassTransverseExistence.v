(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, p. 322: the original
    kernel of xi supplies the independently specified
    transverse normed space and bounded projection. The
    carrier construction is only a local existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier NormedSubspace RealNormUP NormDifferentialUP
  ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexNormPullback
  ComplexModulus HolomorphicLinear ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_transverse_space_exists]: the
    actual splitting X=Cv+ker(xi) has the original eta
    equation and inherited kernel norm, 3.4.6, p. 322.
    Boundedness follows from the actual supplied functional;
    no kernel coordinates or projection estimate are assumed. *)
Theorem complex_weierstrass_transverse_space_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (v:X) (xi:Hom X (ComplexScalars.C R)^o):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) (complex_hom_real xi) ->xi v= 1 ->
  exists K:lmodType (ComplexScalars.C R),exists NK:K->R,is_complex_norm NK /\
    exists inclusion:Hom K X,exists projection:Hom X K,
      is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Proof.
move=>hXi hUnit.
have hZero:xi 0=0:=linear0 xi.
have hAdd x y:xi x=0 ->xi y=0 ->xi (x+y)=0.
  move=>hx hy.
  transitivity (xi x+xi y);first exact:(linearD xi x y).
  by rewrite hx hy addr0.
have hScale c x:xi x=0 ->xi (c*:x)=0.
  move=>hx.
  transitivity (c*xi x);first by rewrite linearZ /=.
  by rewrite hx mulr0.
pose S:=@Subspace (ComplexScalars.C R) X (fun x=>xi x=0) hZero hAdd hScale.
pose K:=[the lmodType (ComplexScalars.C R) of subspace_space S].
pose I:Hom K X:=hom_of_linear (@subspace_inclusion (ComplexScalars.C R) X S).
pose NK:=fun z:K=>NX (I z).
have hNK:is_complex_norm NK:=@complex_norm_injective_precompose R K X NX hNX I
  (@subspace_val_injective (ComplexScalars.C R) X S).
pose eta:=fun x:X=>x-(xi x)*:v.
have hKernel x:S (eta x).
  change (xi (x-(xi x)*:v)=0).
  transitivity (xi x-xi x*xi v);first by rewrite linearB linearZ /=.
  by rewrite hUnit mulr1 subrr.
pose P:=fun x:X=>@subspace_lift (ComplexScalars.C R) X S (eta x) (hKernel x).
have hPValue x:I (P x)=eta x.
  exact:(@subspace_liftE (ComplexScalars.C R) X S (eta x) (hKernel x)).
have hScalar (a b:ComplexScalars.C R):(a*:(b:(ComplexScalars.C R)^o):(ComplexScalars.C R)^o)=a*b:=erefl _.
have hLinear:linear P.
  move=>c x y;apply:subspace_val_injective.
  change (I (P (c*:x+y))=I (c*:P x+P y)).
  transitivity (eta (c*:x+y));first exact:hPValue.
  transitivity (c*:eta x+eta y).
    have hXiLinear:xi (c*:x+y)=c*xi x+xi y:=hom_linear xi c x y.
    rewrite /eta hXiLinear scalerDl scalerBr scalerA opprD !addrA.
    by rewrite [c*:x+y-((c*xi x)*:v)]addrAC.
  transitivity (c*:I (P x)+I (P y));last exact:esym (hom_linear I c (P x) (P y)).
  by rewrite !hPValue.
pose H:Hom X K:=@HomMap (ComplexScalars.C R) X K P (introT (asboolP _) hLinear).
have hProjection x:I (H x)=eta x:=hPValue x.
have hIKernel z:xi (I z)=0:=@subspace_valP (ComplexScalars.C R) X S z.
have hLeft z:H (I z)=z.
  apply:subspace_val_injective;change (I (H (I z))=I z).
  by rewrite hProjection /eta hIKernel scale0r subr0.
have hNorm z:NX (I z)=NK z by [].
have hIBound:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) K)
    (restricted_space (ComplexScalars.embed R) X) NK NX (complex_hom_real I).
  exists 1;split;first exact:ler01.
  by move=>z;rewrite mul1r hNorm.
have [M [hM hBound]]:=hXi.
have hV:0<=NX v:=real_seminorm_nonnegative (complex_norm_real hNX).1 v.
have hHBound:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) K) NX NK (complex_hom_real H).
  exists (1+M*NX v);split;first exact:addr_ge0 ler01 (mulr_ge0 hM hV).
  move=>x.
  have hTri:=real_seminorm_triangle (complex_norm_real hNX).1 x (-((xi x)*:v)).
  rewrite (real_seminorm_negate (complex_norm_real hNX).1) (complex_norm_scale hNX) in hTri.
  have hCoefficient:=ler_wpM2r hV (hBound x).
  have hUpper:=le_trans hTri (lerD (lexx (NX x)) hCoefficient).
  rewrite -hNorm hProjection /eta.
  have hEnd:NX x+(M*NX x)*NX v=(1+M*NX v)*NX x.
    by rewrite mulrDl mul1r mulrAC.
  by rewrite hEnd in hUpper.
exists K,NK;split;first exact:hNK.
exists I,H;constructor.
- exact:hUnit.
- exact:hIKernel.
- exact:hProjection.
- exact:hLeft.
- exact:hNorm.
- exact:hIBound.
- exact:hHBound.
Qed.
