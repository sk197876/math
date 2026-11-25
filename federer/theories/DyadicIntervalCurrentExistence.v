(** Federer (1969), 4.1.12, p. 368: existence
    of the actual original interval series, flatness
    in [0,1/2], and every exact geometric mass-tail
    bound. The original segment currents and complete
    flat space prove the independently specified weak series. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential CurrentSpaces
  CurrentMassSealed NormalCurrentsUP FlatCurrentsUP OrientedSegmentCurrentSealed OrientedSegmentNormal
  OrientedSegmentMass ScalarSegmentCoordinateValues ScalarCurrentIntervalCompact
  DyadicCurrentEndpointArithmetic DyadicIntervalCurrentUP NormalCurrentFinitePrefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DyadicIntervalCurrentExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation C := (@current_space R h2 1%N Full hFull 1%N).
Local Notation K := (scalar_current_compact_interval R 0 (1/2)).
Local Notation term := (@dyadic_interval_current_term R h2).
Local Notation prefix := (@dyadic_interval_current_prefix R h2).
Local Notation M := (@CurrentMass.value R h2 1%N 1%N Full hFull).

(** Source for [dyadic_interval_current_term_normal]: every
    actual original interval is normal with the same
    compact index [0,1/2], supporting Federer 4.1.12,
    p. 368. *)
Theorem dyadic_interval_current_term_normal k:
  @normal_currents_supported_in R h2 1%N Full hFull 1%N K (term k).
Proof.
have[ha [hab hb]]:=@dyadic_current_endpoint_bounds R k.
split.
- exact:(@oriented_segment_current_normal R h2 1%N Full hFull
    (euclidean_one_embed (dyadic_current_left_endpoint R k))
    (euclidean_one_embed (dyadic_current_right_endpoint R k))
    (@scalar_segment_full_domain R (dyadic_current_left_endpoint R k) (dyadic_current_right_endpoint R k))).
- exact:(@scalar_current_segment_interval_support R h2 0 (1/2)
    (dyadic_current_left_endpoint R k) (dyadic_current_right_endpoint R k) (ltW ha) (ltW hab) hb).
Qed.

(** Source for [dyadic_interval_current_term_mass]: the
    kth original current has mass 4^(-k), with
    formal k=n+1, supporting the original series in
    Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_current_term_mass k:
  M (term k)=(dyadic_current_left_endpoint R k)%:E.
Proof.
have[ha [hab hb]]:=@dyadic_current_endpoint_bounds R k.
rewrite /dyadic_interval_current_term oriented_segment_current_mass euclidean_one_norm_coordinate
  /euclidean_one_embed !ffunE.
have hDifference:0<=dyadic_current_right_endpoint R k-dyadic_current_left_endpoint R k by rewrite subr_ge0;exact:ltW hab.
by rewrite (ger0_norm hDifference) dyadic_current_interval_length.
Qed.

(** Source for [dyadic_interval_current_model_exists]: an
    actual flat current has the independently specified
    original interval series and all printed mass tails,
    supporting Federer 4.1.12, p. 368. The
    construction proves existence; its implementation is later sealed. *)
Theorem dyadic_interval_current_model_exists:
  exists S:C,@is_dyadic_interval_current_series R h2 S /\
    @is_flat_current_supported_in R h2 1%N 1%N Full hFull K S /\
    forall k,(M ((S-prefix k)%R)<=(dyadic_current_mass_tail R k)%:E)%E.
Proof.
have hMass k:(M (term k)<=(dyadic_current_mass_tail R k-dyadic_current_mass_tail R k.+1)%:E)%E.
  by rewrite dyadic_interval_current_term_mass dyadic_current_mass_tail_step.
have[S [hFlat [hTail hWeak]]]:=@normal_current_mass_series_exists R h2 1%N 1%N Full hFull K
  term (dyadic_current_mass_tail R) dyadic_interval_current_term_normal
  (dyadic_current_mass_tail_nonnegative R) hMass (@dyadic_current_mass_tail_small R).
exists S;split;first exact:hWeak.
by split.
Qed.

(** Source for [dyadic_interval_current_series_exists]:
    the independently specified current series of
    Federer 4.1.12, p. 368, exists. *)
Theorem dyadic_interval_current_series_exists:exists S:C,@is_dyadic_interval_current_series R h2 S.
Proof. have[S [hS _]]:=dyadic_interval_current_model_exists;by exists S. Qed.
End DyadicIntervalCurrentExistence.
