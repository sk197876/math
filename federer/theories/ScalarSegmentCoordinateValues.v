(** Federer (1969), 4.1.8, p. 362: the
    actual scalar segment in the original R^1
    coordinate identification. Its velocity and path
    are precisely those in the final interval formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals ring.
From Federer Require Import Hom GradedComponents GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate ExteriorAlgebra ExteriorGrading ExteriorPowers FiniteExteriorPowers
  ExteriorFirstPairingTuple CurrentSegmentMapUP ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_coordinate_top_first]: the original
    coordinate top vector in dimension one is the
    original one-vector e_1, supporting the scalar
    interval formula in Federer 4.1.8, p. 362. *)
Lemma scalar_coordinate_top_first (R:realType):
  e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N)=
    exterior_first_inclusion (R_n R 1%N) (@coordinate_basis R 1%N ord0).
Proof.
have hTuple:[tuple of map (@coordinate_basis R 1%N) (ord_tuple 1%N)]=
    [tuple @coordinate_basis R 1%N ord0].
  apply:eq_from_tnth=>i;by rewrite (ord1 i) tnth_map tnth_ord_tuple.
rewrite -exterior_first_single_tuple;apply:val_inj.
change (component_val (e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N))=
  component_val (e_lambda (@idfun (R_n R 1%N)) [tuple @coordinate_basis R 1%N ord0])).
rewrite !e_lambdaE map_id.
exact:(congr1 (@exterior_word R (R_n R 1%N)) (congr1 val hTuple)).
Qed.

(** Source for [scalar_segment_velocity]: the original
    exterior one-vector v-u in R^1 is (v-u)e_1,
    supporting Federer 4.1.8, p. 362. No
    strict endpoint ordering is needed for this identity. *)
Lemma scalar_segment_velocity (R:realType) (u v:R):
  exterior_first_inclusion (R_n R 1%N) (euclidean_one_embed v-euclidean_one_embed u)=
    (v-u)*:e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N).
Proof.
have hVector:euclidean_one_embed v-euclidean_one_embed u=
    (v-u)*:(@coordinate_basis R 1%N ord0).
  apply/ffunP=>i;rewrite (ord1 i) /euclidean_one_embed /coordinate_basis !ffunE eqxx.
  change (v-u=(v-u)*1).
  by rewrite mulr1.
by rewrite hVector linearZ scalar_coordinate_top_first.
Qed.

(** Source for [scalar_segment_parameter_value]: the original
    Euclidean affine path equals the scalar affine
    path under R=R^1, supporting the final interval
    identity in Federer 4.1.8, p. 362. *)
Lemma scalar_segment_parameter_value (R:realType) (u v t:R):
  metric_segment_point (euclidean_one_embed u) (euclidean_one_embed v) t=
    euclidean_one_embed ((v-u)*t+u).
Proof.
apply/ffunP=>i;rewrite /metric_segment_point /euclidean_one_embed !ffunE.
change (u+t*(v-u)=(v-u)*t+u);ring.
Qed.

(** Source for [scalar_segment_full_domain]: the original
    whole scalar line contains every closed segment,
    supporting the final current identity in Federer
    4.1.8, p. 362. *)
Lemma scalar_segment_full_domain (R:realType) (u v:R):
  @is_current_segment_domain R 1%N (fun _=>True) (euclidean_one_embed u) (euclidean_one_embed v).
Proof. by []. Qed.
