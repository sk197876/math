(** Federer (1969), 4.1.12, pp. 368–369:
    finite prefixes of the two original interval-current
    series are normal with the same compact support.
    Reuse the original supported-normal subspace and
    the mass-limit existence theorem for the prefixes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet NormalCurrentsUP NormalCurrentSpaces
  FlatCurrentsUP CompactNormalCurrentMassLimit CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section NormalCurrentFinitePrefix.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation normalK := (@normal_currents_supported_in R h2 n U hU m K).
Local Notation N := (@supported_normal_current_subspace R h2 n U hU m K).

(** Source for [normal_current_finite_prefix_supported]:
    finite prefixes remain in the original N_(m,K),
    supporting the two series of Federer 4.1.12,
    pp. 368–369. The empty prefix is included. *)
Theorem normal_current_finite_prefix_supported (v:nat->C):
  (forall k,normalK (v k))->forall L,normalK (\sum_(k<L) v k).
Proof.
move=>hV;elim=>[|L ih].
- rewrite big_ord0;exact:(subspace_zero N).
- rewrite big_ord_recr /=;exact:(@subspace_add R C N _ _ ih (hV L)).
Qed.

(** Source for [normal_current_mass_series_exists]:
    normal original terms with one compact support
    and vanishing summable mass tails have an actual
    flat current sum, with the original weak series
    specification and quantitative mass tails, supporting
    Federer 4.1.12, pp. 368–369. *)
Theorem normal_current_mass_series_exists (v:nat->C) (t:nat->R):
  (forall k,normalK (v k))->
  (forall k,0<=t k)->
  (forall k,(@CurrentMassSealed.CurrentMass.value R h2 n m U hU (v k)<=(t k-t k.+1)%:E)%E)->
  (forall epsilon:R,0<epsilon->exists k,t k<epsilon)->
  exists S:C,@is_flat_current_supported_in R h2 n m U hU K S /\
    (forall k,(@CurrentMassSealed.CurrentMass.value R h2 n m U hU (S-\sum_(j<k) v j)<=(t k)%:E)%E) /\
    @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(j<k) v j) S.
Proof.
move=>hV hT hMass hSmall.
apply:(@compact_normal_current_mass_limit R h2 n m U hU K
  (fun k=>\sum_(j<k) v j) t (normal_current_finite_prefix_supported hV) hT _ hSmall)=>k.
rewrite big_ord_recr /= addrAC subrr add0r;exact:hMass k.
Qed.
End NormalCurrentFinitePrefix.
