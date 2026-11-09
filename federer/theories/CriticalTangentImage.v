(** Federer (1969), 3.4.2(9), p. 311, proved on
    p. 316: the image of the original tangent-critical
    set is null at degree nu+(mu-nu)/k. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP NormMetric
  RelativeClassUP EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalManifoldClassLaws
  CriticalFlatPiecesUP CriticalFlatCoverUP CriticalFlatDecomposition CriticalManifoldCompactCover
  CriticalRelativeClassLaws CriticalTangentClosed CriticalTangentZeroOscillation
  CriticalOscillationLimit CriticalTangentPieceOscillation CriticalFlatImage
  CriticalCompactImageMass CriticalImageDegreeLaws CriticalOscillation PositiveRightOrderLimit
  RealHausdorffMeasure RealHausdorffMeasureLaws MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_tangent_critical_image_nullity]: the
    complete assertion (9) in 3.4.2, p. 311, proved on
    p. 316. Class one uses compact derivative continuity,
    then (6) and (8). Higher class uses the proved common
    flat cover (7) for the actual derivative functions. At each
    piece (6) and (8), or the finite lower-dimensional image
    estimate, prove nullity in the original degree. Countable
    assembly retains the entire original critical set. The
    target is any normed space; no source measurability, finite
    target basis, completeness, or critical-image conclusion is added. *)
Theorem critical_tangent_critical_image_nullity (R:realType) m d
    (Z:G (R_n R m) d) mu k (S:set (R_n R m))
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R m->Y)
    (hp:0<=(m-d)%:R+(mu-(m-d))%:R/k%:R):
  critical_manifold_family Z mu k S ->(m-d<mu)%N ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f k ->
  @real_hausdorff_measure R (real_norm_metric_space hNY)
    ((m-d)%:R+(mu-(m-d))%:R/k%:R) hp
    (f @` critical_tangent_zero_locus hNY (grassmann_val Z) S f)=0%E.
Proof.
move=>hOmega hDim hf.
have hk:(0<k)%N:=hOmega.2.1.
have [p [g hChart]]:exists (p:euclidean_projection_space R m mu) g,
    is_critical_manifold_chart k (grassmann_val Z) S p g.
  case:hOmega.2.2.2=>[hZero|hChart];last exact:hChart.
  by rewrite hZero ltn0 in hDim.
pose C:=critical_tangent_zero_locus hNY (grassmann_val Z) S f.
have hCS:C `<=` S by move=>x hx;exact:hx.1.
have hF1:=critical_relative_class_lower hk hf.
have hChart1:=critical_manifold_chart_lower_class hk hChart.
have hClosed:=critical_tangent_zero_relatively_closed hChart1 hF1.
case:k hk hOmega hChart hf hp=>[|k] hk hOmega hChart hf hp.
- by [].
pose tau:=(m-d)%:R+(mu-(m-d))%:R/k.+1%:R:R.
pose H:=@real_hausdorff_measure R (real_norm_metric_space hNY) tau hp.
have hH:is_measure H:=@real_hausdorff_measure_is_measure R (real_norm_metric_space hNY) tau hp.
case:(eqVneq k 0%N)=>[hZero|hPositive].
- subst k.
  have [K [hK hUnion]]:=@critical_relatively_closed_compact_cover R m mu 1 S C
    hOmega.2.2.1 hClosed.
  have hNull i:H (f @` K i)=0%E.
    have hKC:K i `<=` C:=(hK i).2.
    have hKS:K i `<=` S by move=>x hx;exact:hCS x (hKC x hx).
    have hZeta:=@critical_tangent_zero_zeta_limit R m mu Y NY hNY
      (grassmann_val Z) S (K i) p g f hChart hKC (hK i).1 hF1.
    have hEta:=@critical_chart_oscillation_zero_limit R m mu Y NY hNY
      (grassmann_val Z) S (K i) p g f 1 hChart hKS (hK i).1 hF1 (lexx 1).
    rewrite subrr in hEta.
    have hEta1:=hEta hZeta.
    have hFamily1:critical_manifold_family Z mu 1 S:=hOmega.
    exact:(@critical_flat_image_nullity R m d Z mu S (K i) Y NY hNY f 1 hp
      hFamily1 hDim hKS (hK i).1 hF1 ltr01 hEta1).
  have hNullUnion:=@measure_null_countable_union R (real_norm_metric_space hNY)
    [the choiceType of (nat:Type)] H hH setT (fun i=>f @` K i) (countableP setT)
    (fun i _=>hNull i).
  apply:(measure_null_subset hH _ hNullUnion).
  move=>y [x hx <-].
  have hxUnion:(\bigcup_i K i) x by rewrite -hUnion.
  have [i _ hxi]:=hxUnion;exists i;first by [].
  by exists x.
- have hkLower:(0<k)%N by rewrite lt0n hPositive.
  have hOmegaLower:=critical_manifold_family_lower_class hkLower (leqnSn k) hOmega.
  have [T [G hCover]]:=@critical_flat_cover_exists R m d Z Y NY hNY mu k S C
    hOmegaLower hClosed.
  have hLambdaR:0<(k.+1%:R:R) by rewrite ltr0n.
  have hTauAbove:(m-d)%:R<tau.
    exact:(@critical_image_degree_above_codimension R (m-d) mu k.+1%:R hLambdaR hDim).
  have hNull i:H (f @` G i)=0%E.
    have hPiece:=critical_flat_cover_pieces hCover i.
    have [hFamily [hTS [hCompact [hGC hLower]]]]:=hPiece.
    have [gamma [hGamma hTFamily]]:=hFamily.
    have hGT:G i `<=` T i by move=>x hx;exact:(hGC x hx).1.
    have hFT:norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
        hNY (T i) (T i) f 1.
      move=>x hx;have [U [F [hxU [hF hAgree]]]]:=hF1 x (hTS x hx).
      exists U,F;split;first exact:hxU.
      split;first exact:hF.
      move=>y hy hyU;split;first exact:hy.
      exact:(hAgree y (hTS y hy) hyU).2.
    case:(eqVneq gamma (m-d)%N)=>[hEqual|hDifferent].
    + have hDegree:gamma%:R<tau by rewrite hEqual.
      exact:(@critical_compact_submanifold_higher_image_null R m gamma 1 (T i) (G i)
        Y NY hNY f tau hp (leqnn 1) hTFamily.2.2.1 hGT hCompact hFT hDegree).
    + have hStrict:(m-d<gamma)%N.
        rewrite ltn_neqAle eq_sym hDifferent hTFamily.1;reflexivity.
      have hEta:=@critical_tangent_piece_oscillation_limit R m d Z mu k Y NY hNY
        S C (T i) (G i) p g f hChart hf (fun x hx=>hx) hPiece.
      have hLambda:0<(k.+1%:R:R) by rewrite ltr0n.
      have hSigma:=@critical_flat_image_degree_nonnegative R m gamma d k.+1%:R hLambda.
      have hLocal:=@critical_flat_image_nullity R m d Z gamma (T i) (G i) Y NY hNY f
        k.+1%:R hSigma hTFamily hStrict hGT hCompact hFT hLambda hEta.
      apply:(@critical_real_hausdorff_null_higher_degree R (real_norm_metric_space hNY)
        ((m-d)%:R+(gamma-(m-d))%:R/k.+1%:R) tau hSigma hp (f @` G i) _ hLocal).
      exact:critical_image_degree_dimension_bound hLambda hGamma.
  have hNullUnion:=@measure_null_countable_union R (real_norm_metric_space hNY)
    [the choiceType of (nat:Type)] H hH setT (fun i=>f @` G i) (countableP setT)
    (fun i _=>hNull i).
  apply:(measure_null_subset hH _ hNullUnion).
  move=>y [x hx <-].
  have hxUnion:(\bigcup_i G i) x by rewrite -(critical_flat_cover_union hCover).
  have [i _ hxi]:=hxUnion;exists i;first by [].
  by exists x.
Qed.
