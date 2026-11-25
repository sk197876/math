(** Federer (1969), 3.1.19, p. 231: the topology of coordinate
    systems and their associated local retractions. The arguments below
    use the actual subspaces and do not require positive class order. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormRegularityOperations
  NormClassZeroTopology MetricSubsetBackground MetricSubsetCorestriction
  HomeomorphismUP RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_class_subdomain_continuous]: general topological
    restriction supporting the coordinate-system statement in Federer
    3.1.19, p. 231. A subset of the open class domain need not be open. *)
Lemma norm_class_subdomain_continuous (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k : S `<=` A -> norm_class hNX hNY A f k ->
    continuous (fun x:metric_subset (fun z:real_norm_metric_space hNX=>S z)=>
      (f (val x):real_norm_metric_space hNY)).
Proof.
move=>hSA hf x W hW.
have hn:=@norm_class_zero_continuous_at R X Y NX NY hNX hNY A f (val x)
  (norm_class_continuous hf) (hSA (val x) (set_valP x)) W hW.
exact (@metric_subset_inclusion_continuous R (real_norm_metric_space hNX) S x _ hn).
Qed.

(** Source for [norm_class_retraction_continuous]: a class-k
    retraction is a continuous retraction, supporting the definition
    following the coordinate-system paragraph of 3.1.19, p. 231. *)
Lemma norm_class_retraction_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (C D:set X) (f:X->X) k :
  is_norm_class_retraction hNX C D f k ->
  @is_metric_retraction R (real_norm_metric_space hNX) C D f.
Proof.
move=>[hf hDC hmap hfix].
refine (@Build_is_metric_retraction R (real_norm_metric_space hNX) C D f hDC hmap hfix _).
apply: metric_subset_corestriction_continuous.
exact (@norm_class_zero_restriction_continuous R X X NX NX hNX hNX C f
  (norm_class_continuous hf)).
Qed.

Section Coordinates.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables (T S:set X) (V:set Y) (phi:X->Y) (psi:Y->X) (k:nat).
Hypothesis hphi:norm_class hNX hNY T phi k.
Hypothesis hpsi:norm_class hNY hNX V psi k.
Hypothesis hS:S `<=` T.
Hypothesis hphiV:forall x, T x -> V (phi x).
Hypothesis him:psi @` V=S.
Hypothesis hcancel:forall u, V u -> phi (psi u)=u.

(** Source for [norm_coordinate_inverse]: the inverse relation
    phi restricted to B intersect T equals psi inverse, in the
    coordinate-system paragraph of 3.1.19, p. 231. Supporting lemma. *)
Lemma norm_coordinate_inverse x : S x -> psi (phi x)=x.
Proof. rewrite -him; move=>[u hu <-]; by rewrite hcancel. Qed.

(** Source for [norm_coordinate_retraction]: psi composed with phi
    retracts T onto B intersect T, Federer 3.1.19, p. 231. This proves
    the class-k laws on the actual open domain T. *)
Lemma norm_coordinate_retraction :
  is_norm_class_retraction hNX T S (fun x=>psi (phi x)) k.
Proof.
constructor=>//.
- exact (@norm_class_compose_on R X Y X NX NY NX hNX hNY hNX T V phi psi k
    hphiV hphi hpsi).
- move=>x hx; rewrite -him; exists (phi x)=>//; exact: hphiV.
- exact: norm_coordinate_inverse.
Qed.

(** Source for [norm_coordinate_forward]: phi on the actual
    subspace B intersect T, with codomain V, in the coordinate-system
    paragraph of 3.1.19, p. 231. Supporting definition. *)
Definition norm_coordinate_forward (x:metric_subset (fun z:real_norm_metric_space hNX=>S z)) :
    metric_subset (fun z:real_norm_metric_space hNY=>V z) :=
  @metric_subset_corestriction R (real_norm_metric_space hNY) _ V
    (fun x=>phi (val x)) (fun x=>@hphiV (val x) (@hS (val x) (set_valP x))) x.

(** Source for [norm_coordinate_backward_range]: the image identity
    in the coordinate-system paragraph of 3.1.19, p. 231, ensures that
    psi takes values in the actual subspace. Supporting lemma. *)
Lemma norm_coordinate_backward_range u : V u -> S (psi u).
Proof. move=>hu; rewrite -him; by exists u. Qed.

(** Source for [norm_coordinate_backward]: psi on V with codomain
    B intersect T, in the coordinate-system paragraph of 3.1.19,
    p. 231. Supporting definition. *)
Definition norm_coordinate_backward (u:metric_subset (fun z:real_norm_metric_space hNY=>V z)) :
    metric_subset (fun z:real_norm_metric_space hNX=>S z) :=
  @metric_subset_corestriction R (real_norm_metric_space hNX) _ S
    (fun u=>psi (val u))
    (fun u=>@norm_coordinate_backward_range (val u) (set_valP u)) u.

(** Source for [norm_coordinate_homeomorphism]: the coordinate
    map phi gives a homeomorphism B intersect T onto V with inverse
    psi, Federer 3.1.19, p. 231. Both subspace maps are continuous. *)
Lemma norm_coordinate_homeomorphism :
  is_homeomorphism_with_inverse norm_coordinate_forward norm_coordinate_backward.
Proof.
constructor.
- apply: metric_subset_corestriction_continuous.
  exact: norm_class_subdomain_continuous hS hphi.
- apply: metric_subset_corestriction_continuous.
  exact (@norm_class_zero_restriction_continuous R Y X NY NX hNY hNX V psi
    (norm_class_continuous hpsi)).
- move=>x; apply: val_inj; change (psi (phi (val x))=val x).
  exact: norm_coordinate_inverse (set_valP x).
- move=>u; apply: val_inj; change (phi (psi (val u))=val u).
  exact: hcancel (set_valP u).
Qed.
End Coordinates.
