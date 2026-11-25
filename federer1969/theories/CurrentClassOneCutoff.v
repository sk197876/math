(** Federer (1969), 4.1.7, p. 358:
    a cutoff equal to one near the
    compact support reduces the boundary formula
    for every original class-one form to
    compact class-one forms. This supporting
    localisation uses the original partition cutoff
    and the previously proved class product law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormDifferentialDirectional
  NormDifferentialLocal NormBoundedLinearTopology NormLinearDomainLaws NormRegularity
  NormCutoffProductClass InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates LinearBasis AlternatingForms
  SmoothCompactSet SmoothCompactDomainInclusion CompactSupportFunctionUP
  SmoothCompactCutoffUP SmoothCompactCutoffSealed ExteriorDerivativeUP ExteriorDifferentialUP
  CurrentCoefficientNorms CurrentClassOneExteriorCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentClassOneCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_class_one_compact_replacement]:
    a compact class-one form agrees with
    phi, together with its actual exterior
    derivative, near the prescribed original compact
    set. This supports the unrestricted class-one
    boundary identity in Federer 4.1.7,
    p. 358; no compact-support hypothesis
    is added to phi itself. *)
Theorem current_class_one_compact_replacement (K:smooth_compact_set hNX U)
    (phi:X->Y) (beta:X->Z):
  norm_class hNX hNY U phi 1%N->
  (forall x,U x->has_exterior_derivative NX NY U phi x (beta x))->
  exists C:smooth_compact_set hNX U,exists psi:X->Y,exists b:X->Z,
    norm_class hNX hNY setT psi 1%N /\
    norm_class_zero NX NZ setT b /\
    (forall x,has_exterior_derivative NX NY setT psi x (b x)) /\
    (forall x,~smooth_compact_carrier C x->psi x=0 /\ b x=0) /\
    exists W:set X,(forall x,W x->norm_domain_interior NX W x) /\
      smooth_compact_carrier K `<=` W /\ W `<=` U /\
      forall x,W x->psi x=phi x /\ b x=beta x.
Proof.
move=>hClass hBeta.
pose chi:=@SmoothCompactCutoff.value R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) U K hU.
have hChi:=@SmoothCompactCutoff.laws R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) U K hU.
pose C:=@Build_smooth_compact_set R X NX hNX U
  (@real_function_support R (real_norm_metric_space hNX) chi)
  (smooth_cutoff_support_in_domain hChi) (smooth_cutoff_compact hChi).
pose psi:=fun x=>chi x*:phi x.
have hPsi:norm_class hNX hNY setT psi 1%N.
  exact:(@norm_class_cutoff_product R X Y NX NY hNX hNY U
    (smooth_compact_carrier C) chi phi 1%N hClass (smooth_cutoff_class hChi 1%N)
    (@real_function_support_closed R (real_norm_metric_space hNX) chi)
    (smooth_compact_in_domain C) (@real_function_zero_off_support R
      (real_norm_metric_space hNX) chi)).
have hOff x:~smooth_compact_carrier C x->psi x=0.
  move=>hx;rewrite /psi (real_function_zero_off_support hx);exact:scale0r.
pose CWhole:=smooth_compact_domain_inclusion (fun (x:X) (_:U x)=>Logic.I) C.
have [b [hContinuous [hExterior hBOff]]]:=
  @current_class_one_exterior_compact R h2 n m CWhole psi hPsi hOff.
have [W [hOpen [hKW hPlateau]]]:=smooth_cutoff_neighbourhood_plateau hChi.
pose O:=W `&` U.
have hO x (hx:O x):norm_domain_interior NX O x.
  have hW:=(@norm_domain_interior_neighbourhood R X NX hNX W x).2
    (open_nbhs_nbhs (conj hOpen hx.1)).
  exact:(@norm_domain_intersection_interior R X NX W U x hW (@hU x hx.2)).
have hAgreement x (hx:O x):psi x=phi x.
  by rewrite /psi /chi (hPlateau x hx.1) scale1r.
exists C,psi,b;split=>//;split=>//;split=>//;split.
- move=>x hx;split;[exact:hOff x hx|exact:hBOff x hx].
- exists O;split;first exact:hO.
  split;first by move=>x hx;split;[exact:hKW x hx|exact:smooth_compact_in_domain K x hx].
  split;first by move=>x hx;exact:hx.2.
  move=>x hx;split;first exact:hAgreement x hx.
  have [L [hL hBL]]:=hExterior x.
  have [M [hM hBM]]:=hBeta x hx.2.
  have hLRestricted:=@norm_differential_restrict R X Y NX NY setT O psi x L
    (fun _ _=>Logic.I) (hO x hx) hL.
  have hPhi:has_norm_differential NX NY O phi x L.
    exact:(norm_differential_domain_agreement hNX hAgreement hLRestricted).
  have hMRestricted:=@norm_differential_restrict R X Y NX NY U O phi x M
    (fun _ h=>h.2) (hO x hx) hM.
  have hSame:=norm_differential_unique hNX hNY hPhi hMRestricted.
  rewrite hSame in hBL;exact:exterior_differential_value_unique hBL hBM.
Qed.
End CurrentClassOneCutoff.
