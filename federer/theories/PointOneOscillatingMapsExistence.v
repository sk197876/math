(** Federer (1969), 4.1.15, p. 373: prove existence
    of the actual bounded-derivative oscillating maps from
    a preceding compact smooth identity bump. The direct
    formula is an existence proof and is hidden by the
    later seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra ring.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocalAgreement NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityLinearMaps
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness CompactSmoothIdentityBump
  PointOneOscillatingMapsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PointOneOscillatingMapsExistence.
Variable R:realType.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Id:=(hom_of_linear (@linear_id R X)).
Local Notation F:=(@compact_smooth_identity_bump R).

(** Source for [point_one_oscillating_maps_exists]: a genuine
    sequence for the final paragraph of 4.1.15, p. 373.
    For s=i+1, take u_i(x)=(-1)^i F(sx)/s.
    Scaling the amplitude and argument cancels exactly in
    the Lipschitz bound and in the derivative at zero. *)
Theorem point_one_oscillating_maps_exists:
  exists u,@is_point_one_oscillating_maps R u.
Proof.
pose s (i:nat):R:=i.+1%:R.
pose sign (i:nat):R:=(-1:R)^+i.
pose u (i:nat) (x:X):X:=(sign i/s i)*:F (s i*:x).
have hS:forall i,0<s i by move=>i;rewrite /s ltr0n.
have hSN:forall i,s i!=0 by move=>i;rewrite gt_eqF.
have hSign:forall i,`|sign i|= 1.
  move=>i;by rewrite /sign normrX normrN normr1 expr1n.
have hCoefficient:forall i,`|sign i/s i|=(s i)^-1.
  move=>i;by rewrite normrM hSign normfV
    (ger0_norm (ltW (hS i))) mul1r.
have hCancel:forall i,(sign i/s i)*s i=sign i.
  move=>i;by rewrite divfK.
have hScaleBound:forall i,norm_bounded_linear NX NX (s i*:Id).
  move=>i;exists (s i);split;first exact:ltW (hS i).
  move=>x;change (is_true (NX (s i*:x)<=s i*NX x)).
  by rewrite inner_normZ (ger0_norm (ltW (hS i))).
have hBoundedSign:forall i,norm_bounded_linear NX NX (sign i*:Id).
  move=>i;exists 1;split;first exact:ler01.
  move=>x;change (is_true (NX (sign i*:x)<= 1*NX x)).
  by rewrite inner_normZ hSign.
have hSmooth:forall i,norm_class_all_orders hNX hNX Full (u i).
  move=>i k.
  have hInner:=@norm_class_precompose_linear R X X X NX NX NX hNX hNX hNX
    Full F (s i*:Id) k (hScaleBound i)
    (@compact_smooth_identity_bump_smooth R k).
  exact:(@norm_class_scale R X X NX NX hNX hNX Full
    (fun x=>F (s i*:x)) (sign i/s i) k hInner).
have [L [hL hLip]]:=@compact_smooth_identity_bump_lipschitz R.
exists u;constructor.
- exact:hSmooth.
- move=>i;by rewrite /u scaler0 compact_smooth_identity_bump_zero scaler0.
- move=>i x;rewrite /u inner_normZ hCoefficient.
  have hInverse:0<=(s i)^-1 by rewrite invr_ge0;exact:ltW (hS i).
  have hScaled:=ler_wpM2l hInverse
    (@compact_smooth_identity_bump_bound R (s i*:x)).
  have hRight:(s i)^-1*2= 2/i.+1%:R by rewrite /s mulrC.
  by rewrite hRight in hScaled.
- move=>i.
  have hLinear:=@norm_differential_linear R X X NX NX hNX hNX
    Full (0:X) (sign i*:Id) (norm_full_domain_interior NX (0:X))
    (hBoundedSign i).
  have hRadius:0<(s i)^-1 by rewrite invr_gt0.
  apply:(@norm_differential_local_agreement R X X NX NX hNX Full Full
    (fun x=>sign i*:x) (u i) (0:X) (sign i*:Id) (s i)^-1
    hRadius _ _ hLinear).
  + by move=>h _;split.
  + move=>h hh _;rewrite add0r /u.
    have hSmall:NX (s i*:h)<= 1.
      rewrite inner_normZ (ger0_norm (ltW (hS i))).
      have hProduct:s i*NX h<1.
        rewrite -[1](mulfV (hSN i)) (ltr_pM2l (hS i)).
        exact:hh.
      exact:ltW hProduct.
    by rewrite (@compact_smooth_identity_bump_plateau R _ hSmall)
      scalerA hCancel.
- exists L;split;first exact:hL.
  move=>i x y;rewrite /u -scalerBr inner_normZ hCoefficient.
  have hPair:=hLip (s i*:x) (s i*:y).
  rewrite -scalerBr inner_normZ (ger0_norm (ltW (hS i))) in hPair.
  have hInverse:0<=(s i)^-1 by rewrite invr_ge0;exact:ltW (hS i).
  have hScaled:=ler_wpM2l hInverse hPair.
  have hExact:(s i)^-1*(L*(s i*NX (x-y)))=L*NX (x-y).
    have hRearrange:(s i)^-1*(L*(s i*NX (x-y)))=
        ((s i)^-1*s i)*(L*NX (x-y)) by ring.
    by rewrite hRearrange (mulVf (hSN i)) mul1r.
  by rewrite hExact in hScaled.
- move=>i x hx;rewrite /u compact_smooth_identity_bump_off ?scaler0 //.
  rewrite inner_normZ (ger0_norm (ltW (hS i))).
  have hOne:1<=s i by rewrite /s ler1n.
  have hProduct:=ler_wpM2r (inner_norm_nonnegative
    (@euclidean_inner_productP R 1%N) x) hOne.
  rewrite mul1r in hProduct;exact:le_trans hx hProduct.
Qed.
End PointOneOscillatingMapsExistence.
