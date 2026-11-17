(** Federer (1969), 3.4.8(11), pp. 334–335:
    the original B_j witnesses and vanishing ideal
    supply a finite-component regular neighbourhood inside
    any prescribed neighbourhood of zero. Common actual
    equations and the nested radii, rather than
    arbitrary restriction of components, prove this choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology NormDifferentialUP NormBoundedLinearTopology
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives SetGermUP GermVanishingSealed
  CommutativeIdealUP AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticPrefixCoordinatesSealed
  GrassmannAbbreviations EuclideanInnerProduct AnalyticPreparedTailUP AnalyticPreparedTailExistence
  FiniteIdealEquationsNeighbourhood AnalyticPreparedFiniteNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NeighbourhoodChoice.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Variable I:set (@analytic_germ_ring R X NX hNX 0).
Variable g:@orthogonal_group R X B hB n e he.
Variable m:nat.
Variable hMN:(m<=n)%N.
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).

(** Source for [analytic_prepared_neighbourhood_choice]:
    the complete original nested neighbourhood can
    be chosen inside the boundary-ordering cover,
    3.4.8(11), pp. 334–335. Its base
    component bound is the preceding induction consequence;
    all source-equation and radius choices are proved. *)
Theorem analytic_prepared_neighbourhood_choice (D:set X) (r0:R):
  is_commutative_ideal I ->~I 1 ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  @analytic_rotated_germ_ideal R X B hB n e he I g `<=`
    @AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 D) ->
  0<r0 ->
  (forall s:R,0<s ->s<=r0 ->finite_set (@connected_component T
      (D `&` [set x|NY (P x)<s]) @` (D `&` [set x|NY (P x)<s]))) ->
  forall W:set X,@open T W ->W 0 ->
    exists O:set X,@open T O /\O 0 /\O `<=` W /\
      finite_set (@connected_component T (O `&` D) @` (O `&` D)).
Proof.
move=>hI hProper hTail hVanish hR0 hBase W hW hW0.
have [degree [U [b [f hPrepared]]]]:=@analytic_prepared_reduction_tail_exists R X B hB n e he omega
  hDual I g m hI hProper hTail.
have hEquations j:@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 D) (analytic_germ (f j)).
  apply:hVanish;exact:analytic_prepared_tail_ideal hPrepared j.
have [E [hE [hE0 hZero]]]:=@finite_ideal_equations_neighbourhood R X NX hNX 0
  (Finite.clone 'I_n _) f D hEquations.
pose W0:set X:=W `&` E.
have hW0Open:@open T W0:=openI hW hE.
have hW00:W0 0 by split.
have hNear:(nbhs (0:T)) W0 by move:hW0Open;rewrite openE;apply.
have [rho [hRho hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX W0 0).2 hNear.
pose r:=Num.min (rho/2) r0.
have hr:0<r by rewrite /r lt_min;apply/andP;split;[by lra|exact:hR0].
have hRRho:r<=rho/2 by rewrite /r ge_min lexx.
have hRR0:r<=r0 by rewrite /r ge_min lexx orbT.
have hClosedBall:[set x|NX x<=r] `<=` W0.
  move=>x hx;change (is_true (NX x<=r)) in hx.
  have hSmall:NX x<rho by lra.
  have h:=hBall x hSmall;by rewrite add0r in h.
have hVanishing (j:'I_n) (hj:(m<=j)%N) x (hx:D x) (hSmall:NX x<=r):
    analytic_representative_value (f j) x = 0.
  exact:hZero j x hx (hClosedBall x hSmall).2.
have hBaseSmall s (hs:0<s) (hSR:s<=r):finite_set (@connected_component T
    (D `&` [set x|NY (P x)<s]) @` (D `&` [set x|NY (P x)<s])).
  exact:hBase s hs (le_trans hSR hRR0).
have [O [hO [hO0 [hClosure hFinite]]]]:=@analytic_prepared_finite_neighbourhood R X B hB n e he
  omega hON hDual I g m degree U b f hPrepared hMN D r hr hVanishing hBaseSmall.
exists O;split;first exact:hO.
split;first exact:hO0.
split.
- move=>x hx;exact:(hClosedBall x (hClosure x (subset_closure hx))).1.
- by rewrite setIC.
Qed.
End NeighbourhoodChoice.
