(** Federer (1969), 3.4.8(8), p. 329:
    the original whole quotient is a finite
    module over the original prefix coefficient
    ring. Iterate the checked image step,
    then use the actual full-prefix surjection. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermUP AnalyticGermRing AnalyticPrefixGermMap AnalyticFullPrefixGerms
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionPrefixImageStep
  CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationSealed CommutativeRingImageQuotient
  RingScalarRestriction RingSubmoduleUP FiniteRingImageStep FiniteModuleSurjectiveImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_finite_original_quotient]:
    the original O_0(X)/I_g is finite over
    Q_m, supporting the printed integral-extension
    assertion of 3.4.8(8), p. 329. Each
    scalar action is the original prefix
    pullback followed by the original quotient.
    No faithful coefficient action is assumed. *)
Theorem analytic_reduction_finite_original_quotient (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (g:@orthogonal_group R X B hB n e he) (C:comNzRingType)
  (pi:{rmorphism [the comNzRingType of (@analytic_germ_ring R X
      (inner_norm hB) (inner_norm_real_norm hB) 0)]->C}) m (hMN:(m<=n)%N):
  is_commutative_ideal I ->~I 1 ->
  is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType
      [the comNzRingType of (@analytic_germ_ring R (R_n R m)
        (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)] of
      ring_restricted_space
        (GRing.RMorphism.clone _ C (pi \o (@analytic_prefix_germ_map R X
          (inner_norm hB) (inner_norm_real_norm hB) n e he omega m hMN)) _) C^o]).
Proof.
move=>hI hProper hPi hAllB.
pose A:=fun p=>[the comNzRingType of (@analytic_germ_ring R (R_n R p)
  (inner_norm (@euclidean_inner_productP R p))
  (inner_norm_real_norm (@euclidean_inner_productP R p)) 0)].
pose E:=fun p (hPN:(p<=n)%N)=>@analytic_prefix_germ_map R X
  (inner_norm hB) (inner_norm_real_norm hB) n e he omega p hPN.
pose F:=fun p (hPN:(p<=n)%N)=>GRing.RMorphism.clone (A p) C (pi \o E p hPN) _.
pose Property:=fun p=>forall (hPN:(p<=n)%N) (D:comNzRingType) (inclusion:{rmorphism D->C}),
    is_commutative_subring_realisation (fun y:C=>exists a:A p,y = F p hPN a) inclusion ->
    exists scalar:{rmorphism A m->D},
      (forall a:A m,inclusion (scalar a) = F m hMN a) /\
      is_finitely_generated_ring_submodule
        (setT:set [the lmodType (A m) of ring_restricted_space scalar D^o]).
have hTower r:Property (m+r)%N.
  elim:r=>[|r IH].
  - rewrite addn0 /Property=>hPN D inclusion hImage.
    have [rho [hTriangle hRho]]:=@commutative_ring_image_quotient (A m) C D (F m hPN) inclusion hImage.
    exists rho;split.
    + move=>a;rewrite hTriangle;by rewrite (bool_irrelevance hPN hMN).
    + exists [::1];constructor.
      * by constructor.
      * by move=>x _.
      * move=>N hN hGenerators d _.
        have hOne:N 1.
          apply:hGenerators;change (1 \in [::(1:D)]);by rewrite inE.
        have [a hA]:=commutative_quotient_surjective hRho d.
        have hScaled:=@ring_submodule_scale (A m) _ N hN a 1 hOne.
        change (N (rho a*1)) in hScaled;by rewrite mulr1 hA in hScaled.
  - rewrite addnS /Property=>hPN D inclusion hImage.
    pose j:'I_n:=Ordinal hPN.
    pose hPrev:=leq_trans (leqnSn (m+r)) hPN.
    pose S0:set C:=fun y=>exists a:A (m+r),y = F (m+r) hPrev a.
    have hS0:is_commutative_subring S0:=commutative_ring_image_subring (F (m+r) hPrev).
    pose D0:=@CommutativeSubringRealisation.space C S0 hS0.
    pose include0:=@CommutativeSubringRealisation.inclusion C S0 hS0.
    have hImage0:=@CommutativeSubringRealisation.laws C S0 hS0.
    have [base [hBase hFinite0]]:=IH hPrev D0 include0 hImage0.
    have hBJ:@analytic_reduction_actual_B R X B hB n e he omega I j g.
      apply:hAllB;by rewrite /j /= leq_addr.
    have hImageStep:is_commutative_subring_realisation
      (fun y:C=>exists a:A (j:nat).+1,y = pi (E (j:nat).+1 (ltn_ord j) a)) inclusion.
      move:hImage;rewrite /F /E (bool_irrelevance hPN (ltn_ord j));by [].
    have [scalar [coordinate [hScalar [_ [hFinite1 _]]]]]:=
      @analytic_reduction_prefix_image_step R X B hB n e he omega hDual I hI hProper
        g C pi hPi j D inclusion hImageStep hBJ.
    have hScalar0 a:inclusion (scalar a) = F (m+r) hPrev a.
      rewrite /F /E (bool_irrelevance hPrev (leq_trans (leqnSn (j:nat)) (ltn_ord j))).
      exact:hScalar.
    have [next [hNext hFinite]]:=@finite_ring_image_step (A m) (A (m+r)) C D0 D
      (F (m+r) hPrev) include0 inclusion _ scalar base hImage0 hImage hScalar0 hFinite0 hFinite1.
    exists next;split;last exact:hFinite.
    move=>a;by rewrite hNext hBase.
have hEnd:(m+(n-m)=n)%N:=subnKC hMN.
have hAtEnd:=hTower (n-m)%N.
rewrite hEnd in hAtEnd.
pose S:set C:=fun y=>exists a:A n,y = F n (leqnn n) a.
have hS:is_commutative_subring S:=commutative_ring_image_subring (F n (leqnn n)).
pose D:=@CommutativeSubringRealisation.space C S hS.
pose inclusion:=@CommutativeSubringRealisation.inclusion C S hS.
have hImage:=@CommutativeSubringRealisation.laws C S hS.
have [scalar [hScalar hFinite]]:=hAtEnd (leqnn n) D inclusion hImage.
pose V:=[the lmodType (A m) of ring_restricted_space scalar D^o].
pose W:=[the lmodType (A m) of ring_restricted_space (F m hMN) C^o].
have hLinear:linear (inclusion:V->W).
  move=>a x y;change (inclusion (scalar a*x+y) = F m hMN a*inclusion x+inclusion y).
  by rewrite rmorphD rmorphM hScalar.
pose f:{linear V->W}:=HB.pack (inclusion:V->W) (GRing.isLinear.Build _ _ _ _ _ hLinear).
have hOnto:forall c:W,exists d:V,f d = c.
  move=>c;have [alpha hAlpha]:=commutative_quotient_surjective hPi c.
  have [beta hBeta]:=@analytic_full_prefix_germ_map_surjective R X B hB n e he hON omega hDual alpha.
  have hMember:S c by exists beta;change (c = pi (E n (leqnn n) beta));by rewrite hBeta hAlpha.
  exact:(commutative_subring_inclusion_image hImage c).1 hMember.
exact:(@finite_module_surjective_linear_image (A m) V W f hOnto hFinite).
Qed.
