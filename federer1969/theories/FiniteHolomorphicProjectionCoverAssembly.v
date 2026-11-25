(** Federer (1969), 3.4.12, p. 339, replacing the ordered
    selections in 3.4.8(10), pp. 332–333: finite fibres, compact
    inverse images and actual holomorphic local inverses give local
    finite holomorphic sheets. Reuse the existing finite branch assembly;
    uniqueness identifies its continuous branches with the original
    holomorphic inverse charts on a smaller neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP ScalarRestriction ComplexScalarSealed
  HolomorphicUP HolomorphicRestriction HolomorphicContinuity HolomorphicFiniteCoverUP
  RelativeLocalInverseUP FiniteFibreEnumerationUP FiniteLocalInverseBranchAssembly
  MetricClosedBalls NormBoundedLinearTopology MetricSubsetBackground EuclideanSubmanifoldUP ContinuousLocalInverseSheetOpen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CoverAssembly.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variable P:Hom X Y.
Variable Z:set XT.
Variable V:set YT.
Variable k:nat.
Variable hP:continuous (fun x:XT=>(P x:YT)).
Variable hV:@open YT V.
Variable hMaps:forall x,Z x ->V (P x).
Variable hFibres:forall y,V y ->exists a:'I_k->XT,is_finite_fibre_enumeration P Z y a.
Variable hCompact:forall y,V y ->exists C:set YT,nbhs y C /\compact [set x:XT|Z x /\C (P x)].
Variable hCharts:forall x,Z x ->exists (U:set XT) (W:set YT) (s:Y->X),
  @is_relative_local_inverse XT YT (fun x:XT=>(P x:YT)) Z x U W s /\@is_holomorphic R Y X NY NX hNY hNX W s.
(** Source for [finite_holomorphic_projection_cover_assembly]: the
    actual original holomorphic local inverse charts extend to precisely
    k disjoint local sheets. Every branch remains holomorphic and its
    image relatively open, 3.4.12, p. 339. *)
Theorem finite_holomorphic_projection_cover_assembly:
  @is_finite_holomorphic_projection_cover R X Y NX NY hNX hNY Z V P k.
Proof.
have hRelative x (hx:Z x):exists U W s,@is_relative_local_inverse XT YT (fun x:XT=>(P x:YT)) Z x U W s.
  have [U [W [s [hS hHolomorphic]]]]:=@hCharts x hx;by exists U,W,s.
constructor.
- move=>x;exact:(continuous_comp (@metric_subset_inclusion_continuous R XT Z x) (@hP (val x))).
- exact:hMaps.
- move=>y hy.
  have [a hEnumeration]:=@hFibres y hy.
  have [C [hCNear hCCompact]]:=@hCompact y hy.
  have [eta [hEtaAt [hEtaContinuous hEtaEnumeration]]]:=
    @finite_local_inverse_branch_assembly R XT YT [the finType of 'I_k] P Z C y a hP hCNear
      hCCompact hEnumeration hRelative.
  have hExists i:exists c:(set XT*set YT*(Y->X))%type,
      @is_relative_local_inverse XT YT (fun x:XT=>(P x:YT)) Z (a i) c.1.1 c.1.2 c.2 /\
        @is_holomorphic R Y X NY NX hNY hNX c.1.2 c.2.
    have [U [W [s [hS hHolomorphic]]]]:=@hCharts (a i) (hEnumeration.1 i).1.
    by exists (U,W,s).
  have [c hC]:=choice hExists.
  pose U:=fun i:'I_k=>(c i).1.1.
  pose W0:=fun i:'I_k=>(c i).1.2.
  pose s:=fun i:'I_k=>(c i).2.
  have hAt i:@is_relative_local_inverse XT YT (fun x:XT=>(P x:YT)) Z (a i) (U i) (W0 i) (s i):=(hC i).1.
  have hW0Near i:nbhs y (W0 i).
    have hW:W0 i y by rewrite -(hEnumeration.1 i).2;exact:(hAt i).2.2.2.1.
    have hOpen:open (W0 i):=(hAt i).2.2.1.
    by rewrite openE in hOpen;exact:hOpen y hW.
  have hUNear i:nbhs y (eta i @^-1` U i).
    have hOpen:open (U i):=(hAt i).2.1.
    have hU:nbhs (eta i y) (U i).
      rewrite hEtaAt;rewrite openE in hOpen;exact:hOpen (a i) (hAt i).1.
    exact:(hEtaContinuous i _ hU).
  have hAllNear:nbhs y [set z|forall i:'I_k,W0 i z /\U i (eta i z)].
    apply:(@filter_forall YT [the finType of 'I_k] _ (nbhs y) (nbhs_filter y))=>i.
    exact:filterI (hW0Near i) (hUNear i).
  have hVNear:nbhs y V.
    have hOpenV:=hV;rewrite openE in hOpenV;exact:hOpenV y hy.
  have hNear:nbhs y [set z|V z /\is_finite_fibre_enumeration P Z z (fun i=>eta i z) /\
      forall i:'I_k,W0 i z /\U i (eta i z)].
    exact:filterI hVNear (filterI hEtaEnumeration hAllNear).
  have [r hR hBall]:=(metricType_numDomainType.nbhs_mdistP y _).1 hNear.
  pose W:set YT:=[set z|mdist y z<r].
  have hOpenW:@open YT W:=metric_open_ball_open y r.
  have hYW:W y.
    change (mdist (y:YT) y<r);by rewrite mdistxx.
  have hData z (hz:W z):V z /\is_finite_fibre_enumeration P Z z (fun i=>eta i z) /\
      forall i:'I_k,W0 i z /\U i (eta i z):=hBall z hz.
  have hEqual i z (hz:W z):s i z=eta i z.
    have hPoint:Z (eta i z) /\P (eta i z)=z:=(hData z hz).2.1.1 i.
    have hInverse:=(hAt i).2.2.2.2.2.1 (eta i z) hPoint.1 ((hData z hz).2.2 i).2.
    by rewrite hPoint.2 in hInverse.
  have hHolomorphic i:@is_holomorphic R Y X NY NX hNY hNX W (s i).
    apply:(@holomorphic_open_restriction R Y X NY NX hNY hNX (W0 i) W (s i) _ _ (hC i).2).
    + move=>z hz;exact:((hData z hz).2.2 i).1.
    + move=>z hz;apply:(@norm_domain_interior_neighbourhood R
        (restricted_space (ComplexScalars.embed R) Y) NY hNY W z).2.
      rewrite openE in hOpenW;exact:hOpenW z hz.
  have hSMaps i z (hz:W z):Z (s i z) /\P (s i z)=z.
    rewrite hEqual //;exact:(hData z hz).2.1.1 i.
  exists W,s;split;first exact:hOpenW.
  split;first exact:hYW.
  split;first by move=>z hz;exact:(hData z hz).1.
  split;first exact:hHolomorphic.
  split;first exact:hSMaps.
  split.
  + move=>i j z hz hSame.
    apply:((hData z hz).2.1.2.2).
    by rewrite -!hEqual.
  + split.
    * move=>x;split.
      -- move=>[hx hPx].
         have [i hI]:=(hData (P x) hPx).2.1.2.1 x hx (erefl _).
         exists i;split;first exact:hPx.
         by rewrite hEqual.
      -- move=>[i [hPx hX]];split;last exact:hPx.
         have hZ:=(hSMaps i (P x) hPx).1;by rewrite hX in hZ.
    * move=>i.
      exact:(@continuous_local_inverse_sheet_open XT YT P Z W (s i) hP hOpenW
        (fun z hz=>@holomorphic_continuous_at R Y X NY NX hNY hNX W (s i) (hHolomorphic i) z hz)
        (hSMaps i) hRelative).
Qed.
End CoverAssembly.
