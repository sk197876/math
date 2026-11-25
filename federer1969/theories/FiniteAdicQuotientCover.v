(** Supporting Federer (1969), 3.4.8(5), p. 328:
    Taylor approximation of the original coefficient ring turns a
    finite module cover into a finite scalar cover of an adic quotient.
    All scalar maps and ideal powers are the given original maps. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingFiniteSynthesis CommutativeIdealUP
  CommutativeQuotientUP CommutativeIdealPowersSealed CommutativeIdealPowersLaws IdealPowerRingMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_adic_quotient_cover]: supporting the original
    coordinate-dimension comparison for Federer 3.4.8(5), p. 328.
    A finite original coefficient-module cover and actual Taylor
    remainder yield a scalar-linear cover with N times as many
    coordinates. Neither a quotient basis nor its dimension is assumed. *)
Theorem finite_adic_quotient_cover (K:fieldType) (D C Q:comNzRingType)
    (constants:{rmorphism K->D}) (psi:{rmorphism D->C}) (scalar:{rmorphism K->C})
    (rho:{rmorphism C->Q}) (I:set D) (M:set C) q N (e:'I_N->C) (J:finType)
    (F:D->{ffun J->K^o})
    (T:{linear {ffun J->K^o}->[the lmodType K of ring_restricted_space constants D^o]}):
  (forall c:K,psi (constants c) = scalar c) ->
  is_commutative_ideal M ->(forall d:D,I d ->M (psi d)) ->
  is_commutative_ideal_quotient (@CommutativeIdealPowers.value C M q) rho ->
  (forall c:C,exists a:{ffun 'I_N->D^o},
    @ring_finite_synthesis D [the lmodType D of ring_restricted_space psi C^o] N e a = c) ->
  (forall d:D,@CommutativeIdealPowers.value D I q (d-T (F d))) ->
  exists g:{linear {ffun ('I_N*J)->K^o}->
    [the lmodType K of ring_restricted_space
      (GRing.RMorphism.clone K Q (rho \o scalar) _) Q^o]},
    forall z:Q,exists c:{ffun ('I_N*J)->K^o},g c = z.
Proof.
move=>hConstants hM hIM hRho hCover hRemainder.
pose V:=[the lmodType K of {ffun ('I_N*J)->K^o}].
pose W:=[the lmodType K of ring_restricted_space
  (GRing.RMorphism.clone K Q (rho \o scalar) _) Q^o].
pose value(c:V):=rho (\sum_(i<N) psi (T [ffun j=>c (i,j)])*e i).
have hLinear:linear (value:V->W).
  move=>a c d.
  have hSlices i:[ffun j=>((a*:c+d):V) (i,j)] =
      a*:[ffun j=>c (i,j)]+[ffun j=>d (i,j)].
    by apply/ffunP=>j;rewrite !ffunE.
  rewrite /value.
  change (rho (\sum_(i<N) psi (T [ffun j=>(a*:c+d) (i,j)])*e i) =
    rho (scalar a)*rho (\sum_(i<N) psi (T [ffun j=>c (i,j)])*e i)+
    rho (\sum_(i<N) psi (T [ffun j=>d (i,j)])*e i)).
  rewrite -rmorphM -rmorphD;apply:congr1.
  rewrite mulr_sumr -big_split;apply:eq_bigr=>i _.
  rewrite hSlices linearP.
  change (psi (constants a*T [ffun j=>c (i,j)]+T [ffun j=>d (i,j)])*e i =
    scalar a*(psi (T [ffun j=>c (i,j)])*e i)+psi (T [ffun j=>d (i,j)])*e i).
  by rewrite rmorphD rmorphM hConstants mulrDl mulrA.
pose g:{linear V->W}:=HB.pack value (GRing.isLinear.Build K V W *:%R value hLinear).
exists g=>z.
have [c hC]:=commutative_quotient_surjective hRho z.
have [a hA]:=hCover c.
exists [ffun p=>F (a p.1) p.2].
change (value [ffun p=>F (a p.1) p.2] = z).
have hValues i:rho (psi (T [ffun j=>[ffun p=>F (a p.1) p.2] (i,j)])) = rho (psi (a i)).
  have hSlice:[ffun j=>[ffun p=>F (a p.1) p.2] (i,j)] = F (a i).
    by apply/ffunP=>j;rewrite !ffunE.
  rewrite hSlice;apply:esym;apply:subr0_eq;rewrite -!rmorphB.
  apply:(commutative_quotient_kernel hRho _).2.
  exact:(@commutative_ideal_power_ring_map D C psi I M hIM q _ (hRemainder (a i))).
rewrite /value rmorph_sum.
have hSum:(\sum_(i<N) rho (psi (T [ffun j=>[ffun p=>F (a p.1) p.2] (i,j)])*e i)) = rho c.
  rewrite -hA.
  change (\sum_(i<N) rho (psi (T [ffun j=>[ffun p=>F (a p.1) p.2] (i,j)])*e i) =
    rho (\sum_(i<N) psi (a i)*e i)).
  rewrite rmorph_sum;apply:eq_bigr=>i _;by rewrite !rmorphM hValues.
by rewrite hSum hC.
Qed.
