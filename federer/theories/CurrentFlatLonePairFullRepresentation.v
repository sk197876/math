(** Federer (1969), 4.1.18, pp. 375–376: the
    quantitative second proposition on all of R^n.
    Follow the original downward induction on current degree.
    The first stage gives a compact L1 coefficient and a flat
    filling in the exact delta/2 tube; the next-degree
    proposition uses the remaining delta/2. Boundary squared
    removes the further filling. Finite mass of T is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentBoundary
  CurrentBoundarySquared CurrentAboveDimension CurrentMassSealed
  CurrentFlatNorm CurrentFlatDualSeminormBasic CurrentFlatMassComparison
  FlatCurrentsUP FlatCurrentFinite SmoothCompactSet EuclideanClosedSupportTube
  CurrentCompactTubeIndex CurrentFlatDensityBoundaryDecomposition
  CompactSummableMultivectors CompactSummableFieldFinitePrefix
  CompactSummableMultivectorDensity CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation UT:=(current_domain R n Full).
Local Notation KType:=(smooth_compact_set hNX Full).
Local Notation C d:=(@current_space R h2 n Full hFull d).
Local Notation W d:=(@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation value d:=(@compact_summable_multivector_value R h2 n d Full hFull).
Local Notation size d:=(@compact_summable_multivector_size R h2 n d Full hFull).
Local Notation D d:=(@compact_summable_multivector_current R h2 n d Full hFull).
Local Notation bd d:=(@current_boundary R h2 n d Full hFull).
Local Notation M d:=(@CurrentMass.value R h2 n d Full hFull).
Local Notation F d K:=(@current_flat_norm R h2 n d Full hFull K).
Local Notation Pairs d:=(@current_lone_pair_space R h2 n d Full hFull).
Local Notation Q d:=(@CurrentLonePair.map R h2 n d Full hFull).
Local Notation J d:=(@current_lone_pair_cost R h2 n d Full hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [current_flat_lone_pair_full_representation]: the
    whole-space instance of the original quantitative second
    proposition in Federer 4.1.18, pp. 375–376. The radius and
    cost allowance are the original delta; E is its exact closed
    neighbourhood. Every ambient and current degree is retained. *)
Theorem current_flat_lone_pair_full_representation m
    (K:KType) (T:C m) (delta:R):
  @is_flat_current_supported_in R h2 n m Full hFull K T->0<delta->
  let E:=@current_compact_closed_tube_index R n Full K delta (fun _ _=>Logic.I) in
  exists v:Pairs m,Q m v=T /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value m v.1 x=0) /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value m.+1 v.2 x=0) /\
    ((J m v)%:E<=F m K T+delta%:E)%E.
Proof.
pose P:=fun d=>forall (K:KType) (T:C d) (delta:R),
  @is_flat_current_supported_in R h2 n d Full hFull K T->0<delta->
  let E:=@current_compact_closed_tube_index R n Full K delta (fun _ _=>Logic.I) in
  exists v:Pairs d,Q d v=T /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value d v.1 x=0) /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value d.+1 v.2 x=0) /\
    ((J d v)%:E<=F d K T+delta%:E)%E.
have hAbove d:(n<d)%N->P d.
  move=>hDegree K0 T0 rho hFlat hRho E.
  have hZero:=@current_above_dimension R h2 n d hDegree Full hFull T0.
  exists 0;split;first by rewrite linear0 hZero.
  split;first by move=>x _;rewrite /compact_summable_multivector_value
    compact_summable_field_value_zero.
  split;first by move=>x _;rewrite /compact_summable_multivector_value
    compact_summable_field_value_zero.
  rewrite (real_seminorm_zero (@current_lone_pair_cost_seminorm R h2 n d Full hFull)).
  have hRhoE:(0<=rho%:E)%E by rewrite lee_fin;exact:ltW hRho.
  exact:adde_ge0 (@current_flat_dual_nonnegative R h2 n d Full hFull K0
    (@current_value R h2 n Full hFull d T0)) hRhoE.
have hStep d:P d.+1->P d.
  move=>hNext K0 T0 rho hFlat hRho E.
  have hHalf:0<rho/2 by rewrite divr_gt0 // ltr0n.
  pose C0:=@current_compact_closed_tube_index R n Full K0 (rho/2) (fun _ _=>Logic.I).
  have[w [Z [hWOff [hZFlat [hDecomposition hCost]]]]]:=
    @current_flat_density_boundary_decomposition R h2 n d phi family hPhi hFamily
      K0 T0 rho hFlat hRho.
  have[v [hZ [hEtaOff [hZetaOff hNextCost]]]]:=hNext C0 Z (rho/2) hZFlat hHalf.
  pose E1:=@current_compact_closed_tube_index R n Full C0 (rho/2) (fun _ _=>Logic.I).
  have hDouble:rho/2+rho/2=rho by field;rewrite ?pnatr_eq0 //.
  have hE1:smooth_compact_carrier E1 `<=` smooth_compact_carrier E.
    move=>x hx.
    have h:=@euclidean_closed_support_tube_nested R n (smooth_compact_carrier K0)
      (rho/2) (rho/2) x hx.
    by rewrite hDouble in h.
  have hC0:smooth_compact_carrier C0 `<=` smooth_compact_carrier E.
    apply:(@euclidean_closed_support_tube_mono R n (smooth_compact_carrier K0)
      (smooth_compact_carrier K0) (rho/2) rho (fun x hx=>hx)).
    lra.
  have hBoundary:bd d Z=bd d (D d.+1 v.1).
    rewrite -hZ (@CurrentLonePair.laws R h2 n d.+1 Full hFull v).
    by rewrite (Bilinear.linD (hom_linear (bd d))) current_boundary_squared addr0.
  have hRepresentation:Q d (w,v.1)=T0.
    rewrite (@CurrentLonePair.laws R h2 n d Full hFull (w,v.1)) /=.
    by rewrite -hBoundary -hDecomposition.
  have hSizeZeta:0<=size d.+2 v.2:=real_seminorm_nonnegative
    (@compact_summable_multivector_size_laws R h2 n d.+2 Full hFull) v.2.
  have hEtaPrice:((size d.+1 v.1)%:E<=F d.+1 C0 Z+(rho/2)%:E)%E.
    apply:(le_trans _ hNextCost).
    rewrite /current_lone_pair_cost /= lee_fin lerDl;exact:hSizeZeta.
  have hZSupport:=@flat_current_supported_support R h2 n d.+1 Full hFull C0 Z hZFlat.
  have hFZ:=@current_flat_norm_le_mass R h2 n d.+1 Full hFull C0 Z hZSupport.
  have hEtaCost:((size d.+1 v.1)%:E<=M d.+1 Z+(rho/2)%:E)%E.
    exact:le_trans hEtaPrice (leeD hFZ (lexx _)).
  have hTotal:((J d (w,v.1))%:E<=F d K0 T0+rho%:E)%E.
    rewrite /current_lone_pair_cost /= EFinD.
    apply:(le_trans (leeD (lexx ((size d w)%:E)) hEtaCost)).
    rewrite addeA.
    have h:=leeD hCost (lexx ((rho/2)%:E)).
    rewrite -!addeA -EFinD hDouble in h.
    rewrite -addeA;exact:h.
  exists (w,v.1);split;first exact:hRepresentation.
  split.
  - move=>x hx;apply:hWOff=>h;apply:hx;exact:hC0 (set_val x) h.
  split.
  - move=>x hx;apply:hEtaOff=>h;apply:hx;exact:hE1 (set_val x) h.
  - exact:hTotal.
have hDown k:forall d,(n<d+k)%N->P d.
  elim:k=>[|k ih] d hBound.
  - apply:hAbove;by move:hBound;rewrite addn0.
  - apply:hStep;apply:ih.
    by rewrite addSn -addnS.
have hAll:P m.
  apply:(hDown n.+1 m).
  by rewrite addnS ltnS leq_addl.
exact:hAll K T delta.
Qed.
End FullRepresentation.
