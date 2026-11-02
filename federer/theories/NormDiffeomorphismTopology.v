(** Federer (1969), 3.1.18, p. 229: the homeomorphism in the
    definition of diffeomorphism, on the actual domain and image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassZeroTopology
  NormRegularity NormDiffeomorphismUP MetricSubsetBackground
  MetricSubsetCorestriction HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Topology.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variables (A : set X) (B : set Y) (f : X->Y) (g : Y->X) (k : nat).
Hypothesis hD : is_norm_diffeomorphism hNX hNY A B f g k.
Local Notation SA := (metric_subset (fun x:real_norm_metric_space hNX=>A x)).
Local Notation SB := (metric_subset (fun y:real_norm_metric_space hNY=>B y)).

(** Source for [norm_diffeomorphism_on_domain]: the map on the
    actual open domain, supporting Federer 3.1.18, p. 229. *)
Definition norm_diffeomorphism_on_domain (x:SA) : SB :=
  @metric_subset_corestriction R (real_norm_metric_space hNY) SA B
    (fun z=>f (val z)) (fun z=>@norm_diffeomorphism_maps R X Y NX NY hNX hNY
      A B f g k hD (val z) (set_valP z)) x.

(** Source for [norm_diffeomorphism_on_image]: the inverse on the
    actual open image, supporting Federer 3.1.18, p. 229. *)
Definition norm_diffeomorphism_on_image (y:SB) : SA :=
  @metric_subset_corestriction R (real_norm_metric_space hNX) SB A
    (fun z=>g (val z)) (fun z=>@norm_diffeomorphism_inverse_maps R X Y NX NY hNX hNY
      A B f g k hD (val z) (set_valP z)) y.

(** Source for [norm_diffeomorphism_homeomorphism]: the abstract
    diffeomorphism laws give a genuine homeomorphism with its named
    inverse, as required by Federer 3.1.18, p. 229. *)
Lemma norm_diffeomorphism_homeomorphism :
  is_homeomorphism_with_inverse norm_diffeomorphism_on_domain norm_diffeomorphism_on_image.
Proof.
constructor.
- apply: metric_subset_corestriction_continuous.
  exact (@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY A f
    (norm_class_continuous (norm_diffeomorphism_forward_class hD))).
- apply: metric_subset_corestriction_continuous.
  exact (@norm_class_zero_restriction_continuous R Y X NY NX hNY hNX B g
    (norm_class_continuous (norm_diffeomorphism_inverse_class hD))).
- move=>x; apply: val_inj; change (g (f (val x))=val x).
  exact (@norm_diffeomorphism_left_inverse R X Y NX NY hNX hNY A B f g k hD
    (val x) (set_valP x)).
- move=>y; apply: val_inj; change (f (g (val y))=val y).
  exact (@norm_diffeomorphism_right_inverse R X Y NX NY hNX hNY A B f g k hD
    (val y) (set_valP y)).
Qed.
End Topology.
