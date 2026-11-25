(** Federer (1969), 4.1.15, p. 373: a Lipschitz
    retraction of compact K onto the subset C gives the
    exact flat-current support equality. Compactness of C
    is a conclusion of the retraction, not an additional
    assumption on the original subset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP RetractionUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentCompactRetractionExtension CurrentFlatLipschitzRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_retraction_set_localisation]: the
    displayed equality F_(m,K) intersect {sptT subset C}=F_(m,C)
    in Federer 4.1.15, p. 373. C is initially an arbitrary
    subset, and the proof supplies its actual compact index
    before applying the preceding localisation law. *)
Theorem current_flat_retraction_set_localisation (R : realType)
    (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (C : set (R_n R n)) (r : R_n R n->R_n R n)
    (hRetraction : @is_metric_retraction R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (smooth_compact_carrier K) C r)
    (hLip : @is_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (smooth_compact_carrier K) r) :
  exists D : smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U,
    smooth_compact_carrier D=C /\
    forall T : @current_space R h2 n U hU m,
      (@is_flat_current_supported_in R h2 n m U hU K T /\
        @current_support R h2 n U hU m T `<=` C) <->
      @is_flat_current_supported_in R h2 n m U hU D T.
Proof.
have [D hD]:=@current_compact_retraction_index_exists R n U hU
  K C r hRetraction hLip.
have hRD:@is_metric_retraction R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (smooth_compact_carrier K) (smooth_compact_carrier D) r.
  by rewrite hD.
exists D;split;first exact:hD.
move=>T.
have hLocalisation:=@current_flat_retraction_localisation R h2 n m U hU
  K D r hRD hLip T.
by rewrite hD in hLocalisation.
Qed.

Arguments current_flat_retraction_set_localisation : clear implicits.
