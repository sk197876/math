(** Federer (1969), 3.2.13, p. 251: beta_t(m,m)= 1,
    the initial value for the projection-constant product formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm AdjointUP AdjointCriteria
  OrthogonalMaps OrthogonalFinite OrthogonalInjectionSpaces OrthogonalProjectionConstants ProjectionBeta ProjectionConstantNorms
  ExteriorNorm ExteriorNormNaturality ExteriorDiameterUP RealPower ExtendedPositivePower
  ProbabilityConstantIntegral MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  PartialFunctionUP CompactGroupHaarNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [square_orthogonal_projection_orthogonal]: a
    square Euclidean orthogonal projection is an orthogonal map,
    1.7.2 and 1.7.4, pp. 28–31, used for beta_t(m,m)
    in Federer 3.2.13, p. 251. *)
Lemma square_orthogonal_projection_orthogonal (R:realType) m
    (p:{linear R_n R m->R_n R m}):
  is_orthogonal_projection (@euclidean_inner_product R m) (@euclidean_inner_product R m) p ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) p.
Proof.
move=>[a [ha hAdj]].
have hCan:cancel a p:=(orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m) hAdj).1 ha.
have [g [hag [hga hg]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m
  (@coordinate_basis R m) (@coordinate_basisP R m) a ha.
have hEq x:p x=g x.
  have h:=hCan (g x); rewrite hga in h; exact:h.
move=>x y; rewrite !hEq; exact:hg x y.
Qed.

(** Source for [projection_constant_diagonal_one]: the value
    one satisfies the defining projection norm laws in equal
    dimensions, Federer 3.2.13, p. 251. *)
Lemma projection_constant_diagonal_one (R:realType) (h2:(1+1:R)!= 0) m (t:R):
  0<t ->is_projection_constant h2 t m m 1.
Proof.
move=>ht; split; first exact:ltr01.
move=>mulS invS eS hS phi hPhi xi hSimple.
have [nu [hNu hRep hm hTotal]]:=normalised_invariant_measure_integral hPhi.
pose N:=exterior_norm h2 (@euclidean_inner_productP R m) xi.
have hN:0<=N:=exterior_norm_nonnegative h2 (@euclidean_inner_productP R m) xi.
have hConst:=@probability_constant_integral R _ phi hm (real_power N t) hPhi.2.
exists (real_power N t)%:E.
- apply:(measure_integral_graph_equivalent _ hConst)=>p z.
  change ((real_power N t)%:E=z <->partial_function_graph
    (real_total_integrand (fun p=>real_power (projection_norm h2 xi p) t)) p z).
  rewrite real_total_integrand_graph /projection_norm.
  have hp:=square_orthogonal_projection_orthogonal (orthogonal_projection_map_projection p).
  by rewrite (exterior_norm_orthogonal_natural h2 (@euclidean_inner_productP R m) (@euclidean_inner_productP R m) hp).
- rewrite /extended_positive_power real_power_root_cancel // mul1r.
  by [].
Qed.

(** Source for [projection_beta_diagonal]: beta_t(m,m)= 1,
    the initial value explicitly used in Federer 3.2.13,
    p. 251. Every finite exponent t>= 1 is covered. *)
Theorem projection_beta_diagonal (R:realType) m (t:R):
  1<=t ->@projection_beta R m m (leqnn m) t%:E= 1.
Proof.
move=>ht; have ht0:0<t:=lt_le_trans ltr01 ht.
have htE:(1<=t%:E)%E by rewrite lee_fin.
exact:(projection_constant_unique (leqnn m) ht0
  (@projection_beta_specification R m m (leqnn m) t%:E htE)
  (projection_constant_diagonal_one (real_exterior_two_nonzero R) m ht0)).
Qed.
