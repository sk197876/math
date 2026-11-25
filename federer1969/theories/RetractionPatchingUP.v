(** Federer (1969), 3.1.20, pp. 232–233: abstract data and
    laws for the countable retraction-patching construction. The
    existence witness is proved privately and sealed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity InnerConvex LocalRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_retraction_patch_family]: the countably indexed
    selected balls and coordinate charts used in Federer 3.1.20,
    p. 232. Empty slots permit finite or empty selections without
    repeating an active ball infinitely often. *)
Record is_retraction_patch_family (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B U:set X) (P Q:nat->set X) k : Prop := {
  (** Source for [patch_family_closed]: P_i are closed balls,
      Federer 3.1.20, p. 232. Empty indexing slots are allowed. *)
  patch_family_closed : forall i,@closed [the topologicalType of real_norm_metric_space hNX] (P i);
  (** Source for [patch_family_open]: Q_i are open balls,
      Federer 3.1.20, p. 232. *)
  patch_family_open : forall i,@open [the topologicalType of real_norm_metric_space hNX] (Q i);
  (** Source for [patch_family_inside]: the Q_i stay in the
      original coordinate-neighbourhood union, 3.1.20, p. 232. *)
  patch_family_inside : forall i,Q i `<=` U;
  (** Source for [patch_family_charts]: each active P_i lies in
      a convex coordinate neighbourhood and has a smooth cutoff
      equal to one on Q_i, 3.1.20, p. 232, by 3.1.13. *)
  patch_family_charts : forall i,(P i=set0 /\ Q i=set0) \/
    exists (T:set X) (V:set Y) (phi:X->Y) (psi:Y->X) (u:X->R^o),
      norm_class hNX hNY T phi k /\ norm_class hNY hNX V psi k /\
      (forall x,T x -> V (phi x)) /\ psi @` V=B `&` T /\
      (forall y,V y -> phi (psi y)=y) /\ is_inner_convex V /\
      norm_class hNX (scalar_absolute_value_norm R) (fun _=>True) u k /\
      (forall x,0<=u x<=1) /\ P i `<=` T /\ Q i `<=` P i /\
      (forall x,~P i x -> u x=0) /\ (forall x,Q i x -> u x = 1)
}.

(** Source for [is_retraction_sequence_step]: the consequences of
    one corrected patching step W_i,f_i to W_(i+1),f_(i+1),
    Federer 3.1.20, pp. 232–233. The patch formula is proved
    separately; these are the laws needed for its limit. *)
Record is_retraction_sequence_step (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B U P Q W W':set X) (f f':X->X) k : Prop := {
  (** Source for [retraction_step_partial]: the corrected
      intermediate map has values in B, 3.1.20, p. 232;
      erratum p. 4, book p. 232 line 11. *)
  retraction_step_partial : is_partial_neighbourhood_retraction hNX B W' f' k;
  (** Source for [retraction_step_inside]: the new domain stays
      in the coordinate-neighbourhood union, 3.1.20, p. 232. *)
  retraction_step_inside : W' `<=` U;
  (** Source for [retraction_step_domain_off]: domains agree
      away from P_i, supporting 3.1.20, p. 233. *)
  retraction_step_domain_off : forall x,~P x -> (W' x <-> W x);
  (** Source for [retraction_step_values_off]: old values persist
      away from P_i, Federer 3.1.20, pp. 232–233. *)
  retraction_step_values_off : forall x,W x -> ~P x -> f' x=f x;
  (** Source for [retraction_step_fixed_set]: the displayed
      identity B intersect W_(i+1)=B intersect (W_i union Q_i),
      Federer 3.1.20, p. 232. *)
  retraction_step_fixed_set : B `&` W'=B `&` (W `|` Q);
  (** Source for [retraction_step_new_domain]: Q_i is included
      in the new open domain, Federer 3.1.20, p. 232. *)
  retraction_step_new_domain : Q `<=` W'
}.

(** Source for [is_retraction_patching_sequence]: the full
    induction in Federer 3.1.20, p. 232, specified by start,
    corrected intermediate retraction laws and successor steps.
    Openness of the eventual domain is proved downstream. *)
Record is_retraction_patching_sequence (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B U:set X) (P Q:nat->set X)
    (W:nat->set X) (f:nat->X->X) k : Prop := {
  (** Source for [patching_initial_domain]: W_0 is empty,
      Federer 3.1.20, p. 232. *)
  patching_initial_domain : W 0=set0;
  (** Source for [patching_initial_map]: f_0=0, Federer 3.1.20,
      p. 232; values on the empty domain carry no constraint. *)
  patching_initial_map : forall x,f 0 x=0;
  (** Source for [patching_partial_maps]: every f_i is class k,
      maps W_i into B and fixes B intersect W_i, 3.1.20,
      p. 232, corrected line 11. *)
  patching_partial_maps : forall i,is_partial_neighbourhood_retraction hNX B (W i) (f i) k;
  (** Source for [patching_domains_inside]: all W_i lie in the
      original coordinate-neighbourhood union, 3.1.20, p. 232. *)
  patching_domains_inside : forall i,W i `<=` U;
  (** Source for [patching_successor]: each step has the exact
      domain, value and fixed-set consequences used in the
      stabilization argument of 3.1.20, pp. 232–233. *)
  patching_successor : forall i,is_retraction_sequence_step hNX B U (P i) (Q i)
    (W i) (W i.+1) (f i) (f i.+1) k
}.
