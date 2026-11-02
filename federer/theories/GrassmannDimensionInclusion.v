(** Federer (1969), 1.6.1–1.6.2, pp. 23–24:
    equal finite dimensions turn subspace inclusion into
    equality. Supporting the comparison of geometric and
    approximate tangent planes in 3.2.28, pp. 265–267. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier SubspaceFamilies
  GrassmannSubspaces LinearBasis FiniteDimension FiniteIndependence FiniteBasisCriterion
  FiniteBasisComparison FiniteDualDimension Annihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [grassmann_equal_dimension_inclusion]: supporting
    equality of the tangent planes in Federer 3.2.28,
    pp. 265–267, by 1.6.1–1.6.2, pp. 23–24.
    Both dimensions are certified by actual bases of
    the abstract subspace carriers. *)
Lemma grassmann_equal_dimension_inclusion (K:fieldType) (V:lmodType K)
    m (P Q:G V m):
  (forall v,grassmann_val P v ->grassmann_val Q v) ->
  forall v,grassmann_val P v <->grassmann_val Q v.
Proof.
move=>hPQ v; split; first exact:hPQ.
move=>hv.
have [b hb]:=grassmann_proof P.
have [c hc]:=grassmann_proof Q.
have hmem i:grassmann_val Q (subspace_val (b i)):=hPQ _ (subspace_valP (b i)).
pose a:=subspace_family hmem.
have hi:finite_independent a.
  apply:subspace_family_independent.
  exact:(@finite_independent_map K [the finType of 'I_m]
    (subspace_space (grassmann_val P)) V (subspace_inclusion (grassmann_val P)) b
    (@subspace_val_injective K V (grassmann_val P)) (finite_basis_independent hb)).
have ha:is_basis a.
  apply:(@finite_independent_basis K (finite_basis_vect hc) m a).
  - by rewrite finite_basis_dimension card_ord.
  - exact hi.
pose w:=@subspace_lift K V (grassmann_val Q) v hv.
pose d i:K:=dual_basis ha i w.
pose z:subspace_space (grassmann_val P):=\sum_i d i*:b i.
have hValue:subspace_val z=v.
  have hh:=congr1 (@subspace_val K V (grassmann_val Q)) (basis_vector_expansion ha w).
  rewrite subspace_liftE linear_sum in hh.
  rewrite /z linear_sum.
  have hSum:(\sum_i subspace_val (d i*:b i))=\sum_i subspace_val (d i*:a i).
    apply:eq_bigr=>i _; by rewrite !linearZ.
  rewrite hSum; exact:esym hh.
rewrite -hValue; exact:subspace_valP z.
Qed.
