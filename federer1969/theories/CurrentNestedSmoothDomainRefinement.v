(** Federer (1969), 4.1.14, p. 371: compare the
    original and smooth intermediate maps on one source
    where both take values in the second map's source.
    The compatible smooth families are first chosen from
    their compact existence laws; then shrink Zf by
    f inverse(Zg). No whole-U image in Zg is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassHigherRestriction NormBoundedLinearTopology NormOpenPreimage
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet SmoothCompactSetExtensionality
  CurrentLipschitzCompactImage CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximationOriginal CurrentSmoothApproximationUP
  CurrentApproximationOpenRestriction CurrentNestedSmoothApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentNestedSmoothDomainRefinement.
Variable R:realType.
Variables n nu omega:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R omega).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Hypothesis hW:forall z,W z->norm_domain_interior NZ W z.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall y,V y->W (g y).
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Variable K:smooth_compact_set hNX U.

(** Source for [current_nested_smooth_domain_refinement_exists]:
    compatible original smooth families on a source where
    both f and all a_i take values in Zg, supporting
    the composition proof in Federer 4.1.14, p. 371.
    The second family retains its whole-Zg Lipschitz bound.
    Both original first/composite family conditions remain
    the printed K-only conditions. *)
Theorem current_nested_smooth_domain_refinement_exists:
  exists E:smooth_compact_set hNY V,
  exists Lg:R,exists Zg:set Y,exists b:nat->Y->Z,
  exists Zf:set X,exists a:nat->X->Y,
  exists hKZf:smooth_compact_carrier K `<=` Zf,
    (forall x,Zf x->norm_domain_interior NX Zf x) /\
    Zf `<=` U /\(forall x,Zf x->Zg (f x)) /\
    (smooth_compact_carrier K=set0->Zf=set0) /\
    (forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)) /\
    @is_current_compact_smooth_approximation R nu omega V W E g Lg Zg b /\
    @is_current_smooth_approximation R n nu Zf Zg
      (@current_compact_index_in_open R n U Zf K hKZf) f a /\
    @is_current_smooth_approximation R n omega Zf W
      (@current_compact_index_in_open R n U Zf K hKZf)
      (fun x=>g (f x)) (fun i x=>b i (a i x)).
Proof.
have[E [Lf [Lg [Zf [Zg [a [b [hInterior [hB hA]]]]]]]]]:=
  @current_nested_compact_smooth_approximations_exists R n nu omega U V W
    hU hV hW f g hFImage hGImage hFLocal hGLocal K.
pose hZf:=current_compact_smooth_domain_open hA.
pose hKZf:=current_compact_smooth_domain_contains hA.
pose hZfU:=@current_compact_smooth_domain_in_domain R n nu U Zg K f Lf Zf a hA.
have hFClass:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hFLocal.
have hFZf:=@norm_class_zero_open_restriction R X Y NX NY U Zf f hZfU hZf hFClass.
have hZgOpen:@open (real_norm_metric_space hNY) Zg.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY Zg y).1
    (@current_compact_smooth_domain_open R nu omega V W E g Lg Zg b hB y hy).
pose Small:set X:=[set x|Zf x /\Zg (f x)].
have hSmallOpen:@open (real_norm_metric_space hNX) Small:=
  @norm_class_zero_open_preimage R X Y NX NY hNX hNY Zf Zg f hFZf hZgOpen.
have hSmall:forall x,Small x->norm_domain_interior NX Small x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX Small x).2
    (open_nbhs_nbhs (conj hSmallOpen hx)).
have hSmallZf:Small `<=` Zf by move=>x [hx _].
have hKSmall:smooth_compact_carrier K `<=` Small.
  move=>x hx;split;first exact:hKZf x hx.
  have hFE:=@norm_domain_interior_member R Y NY hNY
    (smooth_compact_carrier E) (f x) (hInterior x hx).
  exact:(@current_compact_smooth_domain_contains R nu omega V W E g Lg Zg b
    hB (f x) hFE).
pose K0:=@current_compact_index_in_open R n U Zf K hKZf.
pose KS:=@current_compact_index_in_open R n U Small K hKSmall.
have hIndex:@current_compact_index_in_open R n Zf Small K0 hKSmall=KS.
  by apply:smooth_compact_set_extensionality.
have hFInE:forall x,smooth_compact_carrier K x->smooth_compact_carrier E (f x).
  move=>x hx;exact:(@norm_domain_interior_member R Y NY hNY
    (smooth_compact_carrier E) (f x) (hInterior x hx)).
have hFirst0:=@current_compact_smooth_original_approximation R n nu U Zg K f Lf Zf a hA.
have hComposite0:=@current_nested_smooth_composite_approximation R n nu omega
  U V W K E f g Lf Lg Zf Zg a b hB hA hFInE.
have hFirst:=@current_smooth_approximation_open_restriction R n nu Zf Small Zg
  hSmall hSmallZf K0 hKSmall f a hFirst0.
have hComposite:=@current_smooth_approximation_open_restriction R n omega Zf Small W
  hSmall hSmallZf K0 hKSmall (fun x=>g (f x)) (fun i x=>b i (a i x)) hComposite0.
rewrite hIndex in hFirst hComposite.
exists E,Lg,Zg,b,Small,a,hKSmall;split;first exact:hSmall.
split;first by move=>x hx;exact:hZfU x (hSmallZf x hx).
split;first by move=>x [_ hx].
split.
- move=>hEmpty.
  have hZfEmpty:=current_compact_smooth_empty_domain hA hEmpty.
  apply/seteqP;split;last by [].
  move=>x [hx _];by rewrite hZfEmpty in hx.
- split;first exact:hInterior.
  split;first exact:hB.
  by split.
Qed.
End CurrentNestedSmoothDomainRefinement.
