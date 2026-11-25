(** Federer (1969), 4.1.14, p. 370: every allowed
    smooth approximation of a normal current is N bounded.
    The common derivative cap is required only on K. Use
    the earlier support-proper mass and boundary theorems;
    keep zero degree separate from positive-degree boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentBoundary
  CurrentBoundarySupport CurrentSupportGeometry NormalCurrentsUP
  NormalCurrentBoundary CompactRepresentedCurrentMass CurrentMassSealed
  CurrentMassBasic CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentPushforwardSealed CurrentPushforwardBoundary CurrentPushforwardCongruence
  CurrentSmoothApproximationUP CurrentSmoothPushforwardMassBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalSmoothApproximationMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z:set X) (V:set Y).
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX Z.
Variable f:X->Y.
Variable g:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu Z V K f g.
Local Notation C:=(fun m=>@current_space R h2 n Z hZ m).
Local Notation compactSupport:=(fun m (T:C m)=>
  @compact (real_norm_metric_space hNX) (@current_support R h2 n Z hZ m T)).
Local Notation Push:=(fun m (T:C m) (hT:compactSupport m T) i=>
  @current_compact_map_pushforward R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T hT).

(** Source for [current_normal_smooth_approximation_mass_bound]:
    the N-boundedness used before completeness in Federer
    4.1.14, p. 370. The bound exists for every original
    smooth family, without a bound on any open neighbourhood
    of K or a global Lipschitz condition on those maps. *)
Theorem current_normal_smooth_approximation_mass_bound m (T:C m)
    (hNormal:@is_normal_current R h2 n Z hZ m T)
    (hSupport:@current_support R h2 n Z hZ m T `<=` smooth_compact_carrier K):
  exists b:R,0<=b /\forall i,
    (@current_normal_mass R h2 nu V hV m (Push m T hNormal.2 i)<=b%:E)%E.
Proof.
have[c [hc hCap]]:=current_smooth_approximation_bound hG.
case:m T hNormal hSupport=>[|d] T hNormal hSupport.
- have hFinite:=@compact_represented_current_finite_mass R h2 n 0%N
    Z hZ T hNormal.1.1 hNormal.2.
  have[a [ha hA]]:=@current_finite_mass_value R h2 n 0%N Z hZ T hFinite.
  exists a;split;first exact:ha.
  move=>i.
  have h:=@current_smooth_pushforward_mass_bound_on_compact R h2 n nu 0%N
    Z V hZ hV T (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i)
    (@current_compact_map_proper R h2 n nu 0%N Z V hZ T (g i)
      (current_smooth_approximation_image hG i)
      (norm_class_continuous (current_smooth_approximation_class hG i 0%N))
      hNormal.2) hNormal.1.1 K c hc hSupport (hCap i).
  by rewrite hA expr0 mul1e in h.
- pose B:=@current_boundary R h2 n d Z hZ T.
  have hBNormal:=@normal_current_boundary R h2 n Z hZ d T hNormal.
  have hBSupport:@current_support R h2 n Z hZ d B `<=` smooth_compact_carrier K.
    move=>x hx;exact:hSupport x
      (@current_boundary_support_subset R h2 n d Z hZ T x hx).
  have hFinite:=@compact_represented_current_finite_mass R h2 n d.+1
    Z hZ T hNormal.1.1 hNormal.2.
  have hBFinite:=@compact_represented_current_finite_mass R h2 n d
    Z hZ B hNormal.1.2 hBNormal.2.
  have[a [ha hA]]:=@current_finite_mass_value R h2 n d.+1 Z hZ T hFinite.
  have[b [hb hB]]:=@current_finite_mass_value R h2 n d Z hZ B hBFinite.
  exists(c^+d.+1*a+c^+d*b);split.
  + exact:addr_ge0 (mulr_ge0 (exprn_ge0 d.+1 hc) ha)
      (mulr_ge0 (exprn_ge0 d hc) hb).
  move=>i.
  pose fi:=g i.
  pose hImage:=current_smooth_approximation_image hG i.
  pose hSmooth:=current_smooth_approximation_class hG i.
  pose hProper:=@current_compact_map_proper R h2 n nu d.+1 Z V hZ T fi
    hImage (norm_class_continuous (hSmooth 0%N)) hNormal.2.
  pose hBProper:=@current_compact_map_proper R h2 n nu d Z V hZ B fi
    hImage (norm_class_continuous (hSmooth 0%N)) hBNormal.2.
  have hBoundary:@current_boundary R h2 nu d V hV (Push d.+1 T hNormal.2 i)=
      Push d B hBNormal.2 i.
    have h:=@current_pushforward_boundary R h2 n nu d Z V hZ hV
      T fi hImage hSmooth hProper.
    apply:(eq_trans h).
    exact:(@current_pushforward_current_congruence R h2 n nu d Z V hZ hV
      fi hImage hSmooth B B _ hBProper (erefl _)).
  have hMass:=@current_smooth_pushforward_mass_bound_on_compact R h2 n nu d.+1
    Z V hZ hV T fi hImage hSmooth hProper hNormal.1.1 K c hc hSupport (hCap i).
  have hBoundaryMass:=@current_smooth_pushforward_mass_bound_on_compact R h2 n nu d
    Z V hZ hV B fi hImage hSmooth hBProper hNormal.1.2 K c hc hBSupport (hCap i).
  change (@CurrentMass.value R h2 nu d.+1 V hV (Push d.+1 T hNormal.2 i)+
    @CurrentMass.value R h2 nu d V hV
      (@current_boundary R h2 nu d V hV (Push d.+1 T hNormal.2 i))<=
    (c^+d.+1*a+c^+d*b)%:E)%E.
  rewrite hBoundary.
  have h:=leeD hMass hBoundaryMass.
  by rewrite hA hB -!EFinM -EFinD in h.
Qed.
End CurrentNormalSmoothApproximationMass.
