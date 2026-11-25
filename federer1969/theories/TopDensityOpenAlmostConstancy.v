(** Federer (1969), 4.1.26, pp. 383–384:
    the original current constancy conclusion implies
    almost constancy of the scalar top density
    on the same open set. Only original
    local integrability is used; no bound on
    the degree or finite mass is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormClassZeroArithmetic InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading ExteriorDeterminant
  CurrentSpaces CurrentDomain CurrentDensityUP CurrentDensityAction CurrentDensityArithmetic
  CurrentLebesgueDensity EuclideanFundamentalCurrent CurrentLebesgueDensityOpenRestriction
  CurrentOpenDensityConstantAgreement CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentSupportExtensionality EuclideanOpenDomainMeasure OpenSubspaceMeasure
  EuclideanLebesgueDimensions CurrentCoefficientNorms MeasureUP MeasureAlmostUP MeasureAlmostBasic
  FiniteExteriorPowers
  Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_density_open_almost_constant]:
    the scalar inference after the constancy
    theorem in 4.1.26, p. 384. The
    support of T-cE outside the open
    set is exactly the original current-level
    premise supplied by 4.1.7. The almost
    constancy conclusion uses ambient Lebesgue measure. *)
Theorem top_density_open_almost_constant (R:realType)
    (h2:(1+1:R)!=0) m (r:R_n R m->R)
    (hField:@is_locally_integrable_current_density R h2 m m
      (@euclidean_lebesgue_measure R m)
      (fun x=>r x*:e_lambda (@coordinate_basis R m) (ord_tuple m)))
    (T:@full_current_space R h2 m m)
    (hAction:@is_current_density_action R h2 m m (@euclidean_lebesgue_measure R m)
      (fun x=>r x*:e_lambda (@coordinate_basis R m) (ord_tuple m)) T)
    (W:set (R_n R m))
    (hOpen:@open (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) W) c:
  @current_support R h2 m (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x) m
    (T-c*:@euclidean_fundamental_current R h2 m) `<=` ~` W->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) W [set x|r x=c].
Proof.
move=>hSupport.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose top:=e_lambda (@coordinate_basis R m) (ord_tuple m).
pose xi:=fun x:X=>r x*:top.
pose z:=c*:top.
have hW:forall x,W x->norm_domain_interior N W x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X N hN W x).2 (hOpen x hx).
pose WT:=current_domain R m W.
pose mu:=@euclidean_open_domain_measure R m W.
pose hMu:=proj1 (@euclidean_open_domain_measure_laws R m W hW).
pose hRadon:=proj2 (@euclidean_open_domain_measure_laws R m W hW).
pose Rest:=@current_open_restriction R h2 m m W Full hW hFull (fun _ _=>Logic.I).
pose S:=c*:@euclidean_fundamental_current R h2 m.
have hZero:Rest (T-S)=0.
  apply:(@current_empty_support_iff_zero R h2 m m W hW (Rest (T-S))).1.
  rewrite (@current_open_restriction_support R h2 m m W Full hW hFull
    (fun _ _=>Logic.I) (T-S)).
  move=>x [hx hTx];exact:False_ind _ (hSupport x hTx hx).
have hEquality:Rest T=Rest S.
  apply/eqP;rewrite -subr_eq0;apply/eqP.
  by rewrite -(linB (hom_linear Rest)).
have hXiLocal:=@current_lebesgue_density_open_field R h2 m m W hW xi hField.
have hTRep:=@current_lebesgue_density_open_action R h2 m m W hW xi hField T hAction.
have hConstantField:@is_locally_integrable_current_density R h2 m m
    (@euclidean_lebesgue_measure R m) (fun _=>z).
  exact:(@continuous_current_density_integrable R h2 m m (fun _=>z)
    (@norm_class_zero_constant R X (exterior_power X m) N
      (@current_vector_mass R h2 m m) (@current_vector_mass_real_norm R h2 m m)
      Full z hFull)).
have hConstantAction:@is_current_density_action R h2 m m
    (@euclidean_lebesgue_measure R m) (fun _=>z) S.
  exact:(@current_density_scaled_action R h2 m m (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) (fun _=>top)
    (@euclidean_fundamental_current R h2 m) c (@euclidean_fundamental_current_action R h2 m)).
have hSRep:=@current_lebesgue_density_open_action R h2 m m W hW (fun _=>z)
  hConstantField S hConstantAction.
have hAlmost:=@current_open_density_constant_almost_agreement R h2 m m W hW mu
  hMu hRadon (fun x:WT=>xi (set_val x)) hXiLocal z (Rest T) (Rest S)
  hTRep hSRep hEquality.
have hScalar:measure_almost_everywhere mu [set x:WT|r (set_val x)=c].
  apply:(@measure_almost_everywhere_mono R WT mu hMu _ _ _ hAlmost)=>x hx.
  exact:(@top_scalar_injective R h2 m X (@coordinate_basis R m)
    (@coordinate_basisP R m) (r (set_val x)) c hx).
change ((@euclidean_lebesgue_measure R m)
  (set_val @` ~`[set x:WT|r (set_val x)=c])=0%E) in hScalar.
have hImage:((set_val:WT->X) @` (~`[set x:WT|r (set_val x)=c]))=(W `\` [set x:X|r x=c]).
  apply/seteqP;split=>x.
  + move=>[y hy <-];split;[exact:set_valP y|exact:hy].
  + move=>[hx hNot];exists (@exist X (fun z=>z \in W) x (mem_set hx));by [].
by rewrite /measure_almost_everywhere_on -hImage.
Qed.
