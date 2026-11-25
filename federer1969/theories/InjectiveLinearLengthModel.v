(** Federer (1969), 3.2.2, p. 242: an injective differential
    has an invertible source factor with the same vector lengths.
    Erratum p. 4, book p. 242 line 23: the isometric factor
    belongs to O(n,m), with source R^m and target R^n. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP FiniteIndependence LinearBasis FiniteBasisComparison
  PolarFactorisationUP PolarInjection OrthogonalMaps FiniteLinearInverseField
  HomSpaceTopology EuclideanHomOperator LinearRelativeModelTolerance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_injective_length_model]: the polar
    factorization in Federer 3.2.2, p. 242, with the corrected
    isometry direction. The differential's image of a source basis
    provides the required target capacity, so no dimension bound
    is added as a hypothesis. *)
Lemma euclidean_injective_length_model (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) : injective L ->
  exists g:Hom (R_n R m) (R_n R m), injective g /\
    forall v, inner_norm (@euclidean_inner_productP R n) (L v)=
      inner_norm (@euclidean_inner_productP R m) (g v).
Proof.
move=>hL.
have hu:=finite_independent_map hL (finite_basis_independent (@coordinate_basisP R m)).
have [g [h hF]]:=@polar_injection_factorisation_exists R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  (fun i=>L (@coordinate_basis R m i)) hu (hom_as_linear L).
exists (hom_of_linear g); split.
- move=>x y hxy; change (g x=g y) in hxy; apply:hL.
  by rewrite -(injection_factor_equation hF x) -(injection_factor_equation hF y) hxy.
- move=>v; rewrite -(injection_factor_equation hF v).
  exact (orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (injection_factor_orthogonal hF) (g v)).
Qed.

(** Source for [dense_automorphism_length_model]: the choice of
    s from the countable dense set S in Federer 3.2.2,
    p. 242. An explicit positive operator-error neighbourhood
    gives both strict-margin vector bounds. Its existence follows
    from the polar factorization and the bounded inverse of g. *)
Theorem dense_automorphism_length_model (R:realType) m n
    (S:set (Hom (R_n R m) (R_n R m))) :
  (forall g:Hom (R_n R m) (R_n R m),injective g ->
    forall r:R,0<r -> exists s,S s /\ euclidean_operator_norm (s-g)<r) ->
  forall (L:Hom (R_n R m) (R_n R n)) a b,
    injective L -> 0<a -> a<1 -> 1<b -> exists s,S s /\
      forall v,a*inner_norm (@euclidean_inner_productP R m) (s v)<=
        inner_norm (@euclidean_inner_productP R n) (L v) /\
        inner_norm (@euclidean_inner_productP R n) (L v)<=
          b*inner_norm (@euclidean_inner_productP R m) (s v).
Proof.
move=>hS L a b hL ha ha1 hb.
have [g [hg hlen]]:=euclidean_injective_length_model hL.
have [t [hgt htg]]:=finite_injective_linear_inverse_exists (@coordinate_basisP R m) hg.
pose p:=euclidean_operator_norm t.
have hp:0<=p:=hom_operator_norm_nonnegative _ _ _ _.
have hBound v:inner_norm (@euclidean_inner_productP R m) (t v)<=
    p*inner_norm (@euclidean_inner_productP R m) v:=hom_operator_norm_bound _ _ _ _ v.
have [d [hd hNear]]:=linear_relative_model_neighbourhood
  (inner_norm_real_norm (@euclidean_inner_productP R m)) hgt hp hBound ha ha1 hb.
have [s [hs hsg]]:=hS g hg d hd.
exists s; split; first exact hs.
have hErr v:inner_norm (@euclidean_inner_productP R m) (s v-g v)<=
    d*inner_norm (@euclidean_inner_productP R m) v.
  have hh:=hom_operator_norm_bound (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R m) (@coordinate_basisP R m) (s-g) v.
  change (is_true (inner_norm (@euclidean_inner_productP R m) (s v-g v)<=
    euclidean_operator_norm (s-g)*inner_norm (@euclidean_inner_productP R m) v)) in hh.
  apply:le_trans hh _.
  exact (ler_wpM2r (inner_norm_nonnegative _ _) (ltW hsg)).
move=>v; rewrite hlen; exact (hNear s hErr v).
Qed.
