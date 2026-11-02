(** Federer (1969), 3.1.18, pp. 229–230: equality of the kernels of
    Df and p Df when their ranks agree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  SubspaceFamilies LinearBasis FiniteDualDimension Annihilator
  FiniteIndependence FiniteBasisComparison FiniteBasisCriterion FiniteDimension
  IndependentMap SpanningDimension LinearRankUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_composition_equal_rank_kernel]: equality of
    ker Df(x) and ker(p Df(x)) from equal ranks, Federer 3.1.18,
    p. 230, second displayed line. The rank equality alone suffices;
    no orthogonality premise on p is needed. *)
Theorem linear_composition_equal_rank_kernel (K:fieldType)
    (X Y Z:lmodType K) (L:Hom X Y) (p:Hom Y Z) r :
  has_linear_rank L r -> has_linear_rank (hom_comp p L) r ->
  forall x, p (L x)=0 -> L x=0.
Proof.
move=>[b hb] [c hc].
pose W := range_subspace (hom_as_linear L).
pose T := range_subspace (hom_as_linear (hom_comp p L)).
have hex i : exists x:X, p (L x)=subspace_val (c i).
  have [x hx] := subspace_valP (c i); exists x; exact: esym hx.
pose e i := projT1 (cid (hex i)).
have he i : p (L (e i))=subspace_val (c i) by rewrite /e; case: (cid (hex i)).
have hmem i : W (L (e i)) by exists (e i).
pose a := subspace_family hmem.
have ha : finite_independent a.
  move=>d hd.
  have hv := congr1 (fun u:subspace_space W=>p (subspace_val u)) hd.
  rewrite !linear0 !linear_sum in hv.
  have hs : (\sum_i p (subspace_val (d i*:a i)))=\sum_i d i*:subspace_val (c i).
    apply: eq_bigr=>i _; rewrite !linearZ /=.
    exact (congr1 (fun z=>d i*:z) (he i)).
  rewrite hs in hv.
  apply: (finite_basis_independent hc).
  apply: (@subspace_val_injective K Z T).
  rewrite linear_sum linear0.
  under eq_bigr do rewrite linearZ.
  exact hv.
have hab : is_basis a.
  apply: (@finite_independent_basis K (finite_basis_vect hb) r a).
  - by rewrite finite_basis_dimension card_ord.
  - exact ha.
move=>x hx.
have hLx:W (L x) by exists x.
pose u := subspace_lift hLx.
have hu := congr1 subspace_val (basis_vector_expansion hab u).
rewrite subspace_liftE linear_sum in hu.
have hp := congr1 p hu.
rewrite hx linear_sum in hp.
have hs : (\sum_i p (subspace_val ((dual_basis hab i u:K)*:a i)))=
    \sum_i (dual_basis hab i u:K)*:subspace_val (c i).
  apply: eq_bigr=>i _; rewrite !linearZ /=.
  exact (congr1 (fun z=>(dual_basis hab i u:K)*:z) (he i)).
rewrite hs in hp.
have hz : (\sum_i (dual_basis hab i u:K)*:c i)=0.
  apply: (@subspace_val_injective K Z T); rewrite linear_sum linear0.
  under eq_bigr do rewrite linearZ.
  exact: esym hp.
have hd := finite_basis_independent hc hz.
rewrite hu; apply: big1=>i _.
by rewrite hd scale0r linear0.
Qed.
