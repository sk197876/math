(** Federer (1969), 3.2.48, p. 285: choose simple
    unit tangent words whose associated spaces are the
    original tangent planes. Supporting local existence from
    1.6.1, pp. 23–24, and 1.7.5, p. 32;
    no global orientation field or chosen frame is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations InnerProductUP InnerProductRestriction LinearBasis
  GramSchmidt OrthonormalisationUP OrthonormalFamilies ExteriorGrading ExteriorNorm
  FiniteExteriorPowers AssociatedSubspace SimpleElementary SimpleProducts FiniteSpans FiniteSpanSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grassmann_simple_unit_representative]: the actual
    simple unit sigma(x), tau(y) with associated spaces
    S(x), T(y), chosen locally in 3.2.48, p. 285.
    Every actual finite plane has such a representative,
    including the literal unit empty product for the zero plane. *)
Theorem grassmann_simple_unit_representative (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hB:@is_inner_product R V B) r (S:G V r):
  exists x:exterior_power V r,simple x /\exterior_norm h2 hB x= 1 /\
    forall v,FedererSimple.T x v <->grassmann_val S v.
Proof.
pose U:=subspace_space (grassmann_val S).
pose hU:=restricted_inner_productP hB (grassmann_val S).
have [b hb]:=grassmann_proof S.
have [e [he hON]]:=orthonormal_basis_exists hU hb.
have ho:=orthonormalisation_orthonormal hON.
pose d:=fun i:'I_r=>subspace_val (e i).
have hAmbient:orthonormal_family B d by move=>i j; exact (ho i j).
pose x:=e_lambda d (ord_tuple r).
have hUnit:exterior_norm h2 hB x= 1:=orthonormal_product_unit_norm h2 hB hAmbient.
have hNonzero:x!=0.
  apply/eqP=>hz; move:hUnit; rewrite hz exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
have hSpanning:forall u:U,in_finite_span d (subspace_val u).
  apply:(basis_induction he).
  - rewrite linear0; exact:in_finite_span_zero.
  - move=>u v hu hv; rewrite linearD; exact:in_finite_span_add hu hv.
  - move=>a u hu; rewrite linearZ; exact:in_finite_span_scale hu.
  - move=>i; exact (finite_span_generator d i).
exists x; split; first exact:product_simple.
split; first exact hUnit.
move=>v; rewrite (@product_associated_space R h2 V r d hNonzero v); split.
- move=>[a ->].
  elim/big_rec: _=>[|i w _ hw]; first exact:subspace_zero.
  apply:subspace_add; last exact hw.
  apply:subspace_scale; exact (subspace_valP (e i)).
- move=>hv; exact (hSpanning (@subspace_lift R V (grassmann_val S) v hv)).
Qed.
