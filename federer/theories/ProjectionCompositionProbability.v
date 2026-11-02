(** Supporting the final averaging in Federer (1969), 2.10.16, p. 178. For
    fixed q in O*(k,m), composition with q sends theta*_{n,k} to
    theta*_{n,m}. Use the orbit pushforward characterisation of 2.7.16(6),
    p. 139: composing an orbit is the orbit of the composite. This avoids a
    separate choice of a distribution on compositions.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerProductUP Hom TensorUP AdjointUP Adjoint OrthogonalEuclidean
  OrthogonalInjectionSpaces OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HomogeneousSpaceUP
  CompactGroupHaarNormalisation CompactGroupHomogeneousMeasures
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanProjectionComposition OrthogonalProjectionProbability MeasurePushforward
  MeasureBijectionCoordinateTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_probability_orbit]: supporting
    actual orbit law of 2.7.16(6), p. 139, used to
    average composite projections in 2.10.16, p. 178.
    The chosen group presentation and Haar measure are arbitrary. *)
Lemma projection_probability_orbit (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (mulO : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
    (invO : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
    (eO : euclidean_orthogonal_group R n)
    (hO : is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulO invO eO)
    (theta : set (euclidean_orthogonal_group R n) -> \bar R)
    (p : orthogonal_projection_metric_space R n m) :
  is_normalised_haar_measure mulO theta ->
  measure_pushforward (orbit_map (orthogonal_projection_action
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO) p)
    theta=@orthogonal_projection_probability R n m hmn.
Proof.
move=> htheta.
have [phi [hphi huniq hall]] := @euclidean_theta_star_nm_exists_unique R n m mulO invO eO hO hmn.
have hstar := @orthogonal_projection_probability_specification R n m hmn mulO invO eO hO.
have he := huniq _ hstar.
by rewrite (hall theta p htheta) -he.
Qed.

(** Source for [projection_composition_probability]: supporting
    marginal law for the last formula of 2.10.16, p. 178.
    For each fixed q, the actual pushforward is theta*_{n,m},
    independently of q. The proof uses only the composition
    evaluation law and the existing normalised Haar existence. *)
Theorem projection_composition_probability (R : realType) (n k m : nat)
    (hkn : (k<=n)%N) (hmk : (m<=k)%N)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m) :
  is_euclidean_projection_composition C -> forall q,
  measure_pushforward (fun p => C (q,p)) (@orthogonal_projection_probability R n k hkn)=
    @orthogonal_projection_probability R n m (leq_trans hmk hkn).
Proof.
move=> hC q.
have [mulO [invO [eO hO]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [theta htheta] := orthogonal_normalised_haar_measure_exists hO.
have [f hf] := @euclidean_orthogonal_injection_exists R n k hkn.
pose a := inner_adjoint (@euclidean_inner_productP R k) (@euclidean_inner_productP R n)
  (@coordinate_basisP R k) f.
have ha : is_orthogonal_projection (@euclidean_inner_product R n) (@euclidean_inner_product R k) a.
  exists f; split=> //; exact: inner_adjointP.
pose p := orthogonal_projection_of (@euclidean_inner_productP R k) (@euclidean_inner_productP R n)
  (@coordinate_basisP R n) ha.
pose Ak := orthogonal_projection_action (@euclidean_inner_productP R k)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO.
pose Am := orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO.
have he : (fun g => C (q,Ak g p))=orbit_map Am (C (q,p)).
  apply/funext=> g; apply: orthogonal_projection_ext=> x.
  change (euclidean_projection_linear (C (q,Ak g p)) x=
    euclidean_projection_linear (Am g (C (q,p))) x).
  rewrite (hC q (Ak g p) x).
  change (euclidean_projection_linear q (euclidean_projection_linear p
      (orthogonal_element_map (invO g) x))=
    euclidean_projection_linear (C (q,p)) (orthogonal_element_map (invO g) x)).
  exact: esym (hC q p _).
rewrite -(@projection_probability_orbit R n k hkn mulO invO eO hO theta p htheta)
  measure_pushforward_composition he.
exact: projection_probability_orbit htheta.
Qed.
