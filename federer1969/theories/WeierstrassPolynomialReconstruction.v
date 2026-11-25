(** Federer (1969), 3.4.6, pp. 323–324: an
    actual analytic germ with all high mixed rows zero
    has the original neighbourhood polynomial condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticOperations
  AnalyticGermNeighbourhood AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws
  AnalyticDirectionalCoefficient WeierstrassTransverseUP WeierstrassCoefficientUP
  WeierstrassCoefficientExistence WeierstrassSplitInjective WeierstrassDivisionUP
  WeierstrassFiniteRemainderDomain WeierstrassFiniteRemainderCoefficients WeierstrassFiniteRemainderVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_polynomial_reconstruction]:
    the finite low rows give an actual representative
    whose derivatives of every order at least k vanish
    along the original direction on one neighbourhood,
    3.4.6, pp. 323–324. Actual divided fields
    supply the transverse coefficients. Taylor injectivity
    proves equality with the original germ. *)
Theorem weierstrass_polynomial_reconstruction (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (rho:analytic_germ_space hNX (0:X)) (r:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall i j,is_weierstrass_split_coefficient rho v inclusion i j (r i j)) ->
  (forall i,(k<=i)%N ->forall j z,r i j z=0) ->
  @is_directional_polynomial_germ R X NX hNX k v rho.
Proof.
move=>hSplit hXi hR hHigh.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have [f hRep]:=@analytic_germ_has_representative R X NX hNX 0 rho.
pose F:=analytic_representative_value f.
have [U [haU [_ [_ hf]]]]:=@analytic_germ_open_representative R X R^o NX N hNX hN
  setT F 0 (analytic_representative_analytic f).
have hEach i:exists C:X->R,
    @is_analytic_directional_coefficient R X R^o NX N hNX hN U F i v C /\
    @norm_analytic R X R^o NX N hNX hN U C.
  exact:(@analytic_directional_coefficient_exists R X R^o NX N hNX hN U F i v hf).
have [C hC]:=choice hEach.
have [A [haA [hAU [hOpen hFinite]]]]:=@weierstrass_finite_remainder_domain R X K NX NK hNX hNK
  v xi inclusion projection U F k C hSplit hXi haU hf (fun i=>(hC i).2).
pose G:=fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x)).
have [g hG]:=@analytic_representative_from_domain R X NX hNX 0 A G (hFinite 0 haA).
have hValues:analytic_representative_value g=G:=hG.
pose beta:=analytic_germ g.
have [s hS]:=@weierstrass_split_coefficients_exist R X K NX hNX beta v inclusion.
have hg:@norm_analytic R X R^o NX N hNX hN A (analytic_representative_value g).
  by rewrite hValues.
have hCoefficients:=@weierstrass_finite_remainder_coefficients R X K NX NK hNX
  v xi inclusion projection k rho beta f g U A C r s hSplit hRep (erefl _) haU haA hf hg hC (fun x=>congr1 (fun f:X->R=>f x) hG) hR hS.
have hEqual:rho=beta.
  apply:(@weierstrass_split_coefficients_injective R X K NX NK hNX v xi inclusion projection
    rho beta r s hSplit hR hS)=>i j z.
  rewrite hCoefficients.
  case hi:(i<k)%N=>//.
  have hLarge:(k<=i)%N by rewrite leqNgt hi.
  exact:hHigh i hLarge j z.
exists g;split;first exact:esym hEqual.
exists A;split;first exact:haA.
split;first exact:hg.
rewrite hValues.
exact:(@weierstrass_finite_remainder_vanishing R X K NX NK hNX v xi inclusion projection
  k C A hSplit hFinite).
Qed.
