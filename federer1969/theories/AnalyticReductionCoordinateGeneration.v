(** Federer (1969), 3.4.8(8), p. 329:
    the original whole quotient is generated
    by the original prefix coefficients and
    remaining coordinate classes. Apply the
    checked simple prefix step and the
    original least-subring laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermUP AnalyticGermRing AnalyticPrefixGermMap AnalyticFullPrefixGerms AnalyticCoordinateGermsSealed
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionPrefixImageStep
  CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationSealed CommutativeRingImageQuotient CommutativeSubringPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_original_coordinate_generators]:
    p(Q_m) and the original remaining p(gamma_j)
    generate the original O_0(X)/I_g as a ring,
    3.4.8(8), p. 329. Preparation and division
    supply each simple step; no coordinate
    generation conclusion is a premise. *)
Theorem analytic_reduction_original_coordinate_generators (R:realType) (X:lmodType R)
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
  is_generated_commutative_subring
    (fun y:C=>(exists a:@analytic_germ_ring R (R_n R m)
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) 0,
      y = pi (@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB)
        n e he omega m hMN a)) \/
      exists j:'I_n,(m<=j)%N /\
        y = pi (@AnalyticCoordinateGerms.value R X (inner_norm hB) (inner_norm_real_norm hB)
          n e he omega j)) setT.
Proof.
move=>hI hProper hPi hAllB.
pose A:=fun p=>[the comNzRingType of (@analytic_germ_ring R (R_n R p)
  (inner_norm (@euclidean_inner_productP R p))
  (inner_norm_real_norm (@euclidean_inner_productP R p)) 0)].
pose E:=fun p (hPN:(p<=n)%N)=>@analytic_prefix_germ_map R X
  (inner_norm hB) (inner_norm_real_norm hB) n e he omega p hPN.
pose F:=fun p (hPN:(p<=n)%N)=>GRing.RMorphism.clone (A p) C (pi \o E p hPN) _.
constructor.
- by constructor.
- by move=>y _.
- move=>N hN hGenerators c _.
  pose Property:=fun p=>forall (hPN:(p<=n)%N) (a:A p),N (F p hPN a).
  have hTower r:Property (m+r)%N.
    elim:r=>[|r IH].
    + rewrite addn0 /Property=>hPN a.
      apply:hGenerators;left;exists a.
      by rewrite (bool_irrelevance hPN hMN).
    + rewrite addnS /Property=>hPN a.
      pose j:'I_n:=Ordinal hPN.
      pose S:set C:=fun y=>exists b:A (m+r).+1,y = F (m+r).+1 hPN b.
      have hS:is_commutative_subring S:=commutative_ring_image_subring (F (m+r).+1 hPN).
      pose D:=@CommutativeSubringRealisation.space C S hS.
      pose inclusion:=@CommutativeSubringRealisation.inclusion C S hS.
      have hImage:=@CommutativeSubringRealisation.laws C S hS.
      have hBJ:@analytic_reduction_actual_B R X B hB n e he omega I j g.
        apply:hAllB;by rewrite /j /= leq_addr.
      have hImageStep:is_commutative_subring_realisation
        (fun y:C=>exists b:A (j:nat).+1,y = pi (E (j:nat).+1 (ltn_ord j) b)) inclusion.
        have hSets:S = (fun y:C=>exists b:A (j:nat).+1,y = pi (E (j:nat).+1 (ltn_ord j) b)).
          by rewrite /S /F /E (bool_irrelevance hPN (ltn_ord j)).
        by rewrite -hSets.
      have [scalar [coordinate [hScalar [hCoordinate [_ hGenerated]]]]]:=
        @analytic_reduction_prefix_image_step R X B hB n e he omega hDual I hI hProper
          g C pi hPi j D inclusion hImageStep hBJ.
      have hPre:=commutative_subring_ring_preimage inclusion hN.
      have hAll:setT `<=` inclusion @^-1` N.
        apply:(generated_commutative_subring_minimal hGenerated hPre)=>d [->|[b ->]].
        * change (N (inclusion coordinate));rewrite hCoordinate.
          apply:hGenerators;right;exists j;split;last by [].
          by rewrite /j /= leq_addr.
        * change (N (inclusion (scalar b)));rewrite hScalar.
          have hPrevious:=IH (leq_trans (leqnSn (j:nat)) (ltn_ord j)) b.
          exact:hPrevious.
      have hMember:S (F (m+r).+1 hPN a) by exists a.
      have [d hD]:=(commutative_subring_inclusion_image hImage _).1 hMember.
      have hResult:=hAll d Logic.I;change (N (inclusion d)) in hResult.
      by rewrite hD in hResult.
  have hEnd:(m+(n-m)=n)%N:=subnKC hMN.
  have hLast:=hTower (n-m)%N;rewrite hEnd in hLast.
  have [alpha hAlpha]:=commutative_quotient_surjective hPi c.
  have [beta hBeta]:=@analytic_full_prefix_germ_map_surjective R X B hB n e he hON omega hDual alpha.
  have hResult:=hLast (leqnn n) beta.
  change (N (pi (E n (leqnn n) beta))) in hResult.
  by rewrite hBeta hAlpha in hResult.
Qed.
