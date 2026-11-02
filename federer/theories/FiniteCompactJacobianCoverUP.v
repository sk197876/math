(** Federer (1969), 3.2.39, p. 275: independent
    laws for the finite compact source family selected before
    passing to multiplicity layers. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric JacobianDensityMeasure HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_compact_jacobian_cover]: the two
    finite-family assertions in Federer 3.2.39, p. 275,
    together with the exact original source cover used on
    p. 276. The family is specified independently of its
    existence proof. All images and integral values are actual;
    no finite approximation is assumed in the final theorem. *)
Record is_finite_compact_jacobian_cover (R:realType) m n (I:finType)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (A:set (inner_metric_space (@euclidean_inner_productP R m))) (e:R)
    (C:I->set (inner_metric_space (@euclidean_inner_productP R m))):Prop:={
  (** Source for [jacobian_cover_compact]: closed subsets of
      the original compact A in Federer 3.2.39, p. 275. *)
  jacobian_cover_compact:forall i,compact (C i);
  (** Source for [jacobian_cover_subset]: original source
      inclusion in Federer 3.2.39, p. 275. *)
  jacobian_cover_subset:forall i,C i `<=` A;
  (** Source for [jacobian_cover_union]: exact source
      coverage yielding S_1=W in Federer 3.2.39, p. 276. *)
  jacobian_cover_union:(\bigcup_i C i)=A;
  (** Source for [jacobian_cover_mass_sum]: the first
      displayed finite-family equality in Federer 3.2.39,
      p. 275, with the actual Jacobian density measure. *)
  jacobian_cover_mass_sum:(\sum_i euclidean_jacobian_measure f (C i))=euclidean_jacobian_measure f A;
  (** Source for [jacobian_cover_image_cost]: the second
      displayed finite-family approximation in Federer 3.2.39,
      p. 275, in additive finite-error form. *)
  jacobian_cover_image_cost:euclidean_jacobian_measure f A<=
    (\sum_i @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` C i))+e%:E
}.

(** Source for [finite_compact_jacobian_cover_image_union]: the
    exact image union S_1=W in Federer 3.2.39, p. 276.
    It follows from the independent cover law and actual images,
    with no injectivity or measurability premise. *)
Lemma finite_compact_jacobian_cover_image_union (R:realType) m n (I:finType)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A e
    (C:I->set (inner_metric_space (@euclidean_inner_productP R m))):
  is_finite_compact_jacobian_cover f A e C ->(\bigcup_i f @` C i)=f @` A.
Proof.
move=>hCover; rewrite -(jacobian_cover_union hCover).
apply/seteqP; split.
- move=>y [i _ [x hx <-]]; exists x; [by exists i|reflexivity].
- move=>y [x [i _ hx] <-]; exists i; first exact Logic.I.
  by exists x.
Qed.
