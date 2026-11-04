(** Federer (1969), 3.2.48, pp. 285–286: the
    starred tangent words in the isotropy average. Supporting
    application of the complementary orthonormal basis formula
    in 1.7.8, p. 34, retaining orientation signs
    and literal empty products in degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerExterior
  InnerExteriorBasis InnerExteriorPositivity ExteriorNorm ExteriorGrading
  ExteriorHomogeneousProducts ExteriorIndices InitialIndices FiniteExteriorPowers
  LinearBasis OrthonormalFamilies SimpleElementary SimpleAdaptedBasis
  SimpleOrthonormalBasis AssociatedSubspace UnitTopVolume HodgeMaps HodgeBasis
  HodgeIsometry InteriorSigns TopComplements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_indexed_product_unit_norm]: supporting
    complementary unit words in 1.7.8, p. 34, used
    in 3.2.48, p. 286. Every increasing subword of
    an actual orthonormal family has norm one, including
    the empty subword. *)
Lemma orthonormal_indexed_product_unit_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hB:@is_inner_product R V B) n (e:'I_n->V)
    (ho:orthonormal_family B e) p (lambda:Lambda n p):
  exterior_norm h2 hB (e_lambda e (val lambda))= 1.
Proof.
apply:inner_norm_value; first exact:ler01.
have h:=@exterior_orthonormal_family R h2 V B hB n e ho p lambda lambda.
rewrite eqxx in h; rewrite expr1n; exact (esym h).
Qed.

(** Source for [hodge_unit_simple_factor]: the simple unit
    complementary words used in the isotropy average of
    3.2.48, p. 286, by the basis formula of
    1.7.8, p. 34. The orientation factor has absolute
    value one and is retained explicitly: a negative scalar
    empty product is not called a literal simple zero-vector.
    Thus zero and top degrees require no convention change. *)
Theorem hodge_unit_simple_factor (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hB:@is_inner_product R V B) n (e:'I_n->V)
    (he:is_basis e) (E:exterior_power V n) (hE:exterior_norm h2 hB E= 1)
    p (hp:(p<=n)%N) (x:exterior_power V p):
  simple x ->exterior_norm h2 hB x= 1 ->
  exists (z:exterior_power V (n-p)) (c:R),
    simple z /\exterior_norm h2 hB z= 1 /\`|c|= 1 /\
    hodge_vector h2 hB E hp x=c*:z.
Proof.
move=>hSimple hUnit.
have hx:x!=0.
  apply/eqP=>hZero; move:hUnit; rewrite hZero exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
have [d [a [hd [ho [ha hWord]]]]]:=
  @simple_orthonormal_adapted_basis R h2 V B hB n e he p hp x hx hSimple.
have [b [hVolume _]]:=@unit_top_volume_scalar R h2 V B hB n d hd ho E hE.
pose lambda:=Lambda_initial hp.
pose z:=e_lambda d (val (top_complement lambda)).
pose c:=b*a*(-1:R)^+(FedererInteriorSigns.N lambda (top_complement lambda)).
have hZSimple:simple z:=indexed_product_simple d _.
have hZUnit:exterior_norm h2 hB z= 1:=orthonormal_indexed_product_unit_norm h2 hB ho _.
have hValue:hodge_vector h2 hB E hp x=c*:z.
  rewrite hVolume hodge_vector_volume_scale hWord linearZ.
  change (b*:(a*:hodge_vector h2 hB (e_lambda d (ord_tuple n)) hp
    (e_lambda d (val (Lambda_initial hp))))=c*:z).
  rewrite (@hodge_vector_basis R h2 V B hB n d hd ho p hp (Lambda_initial hp)).
  by rewrite !scalerA.
have hC:`|c|= 1.
  have hNorm:=@hodge_vector_norm R h2 V B hB n e he E hE p hp x.
  by rewrite hValue exterior_norm_scale hZUnit hUnit mulr1 in hNorm.
by exists z,c; repeat split.
Qed.
