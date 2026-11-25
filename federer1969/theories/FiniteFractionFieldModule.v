(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the field of fractions
    of the original finite algebra is a
    finite module over any coefficient subfield
    containing the original scalar image. Reuse
    finite module laws and finite linear inverses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis RingScalarRestriction
  RingSubmoduleUP RingSubmoduleSealed RingModuleFiniteLift FiniteFieldModuleBasis
  FiniteInvariantFractionInverse FractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_algebra_fraction_field_module]:
    the finite field extension L/M used
    in 3.4.8(8), pp. 329–330. The
    M-span of the original finite algebra
    generators contains the original algebra and
    is stable under its multiplication. Existing
    finite-dimensional inversion supplies every original
    denominator inverse, so that span contains
    the actual whole fraction field. *)
Theorem finite_algebra_fraction_field_module (A C:comNzRingType) (M L:fieldType)
  (scalar:{rmorphism A->C}) (include:{rmorphism C->L})
  (eta:{rmorphism A->M}) (phi:{rmorphism M->L}):
  is_commutative_fraction_field include ->
  (forall a:A,phi (eta a) = include (scalar a)) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space scalar C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType M of ring_restricted_space phi L^o]).
Proof.
move=>hFraction hTriangle [F hF].
pose V:=[the lmodType M of ring_restricted_space phi L^o].
pose images:seq V:=map include F.
pose W:=@GeneratedRingSubmodule.value M V [set v|v \in images].
have hW:=@GeneratedRingSubmodule.laws M V [set v|v \in images].
have hLaws:=generated_ring_submodule_laws hW.
have hOriginal:forall c:C,W (include c).
  pose P:set [the lmodType A of ring_restricted_space scalar C^o]:=fun c=>W (include c).
  have hP:is_ring_submodule P.
    constructor.
    - change (W (include 0));rewrite rmorph0;exact:ring_submodule_zero hLaws.
    - move=>c d hC hD;change (W (include (c+d)));rewrite rmorphD.
      exact:(@ring_submodule_add M V W hLaws _ _ hC hD).
    - move=>c hC;change (W (include (-c)));rewrite rmorphN.
      exact:(@ring_submodule_opp M V W hLaws _ hC).
    - move=>a c hC;change (W (include (scalar a*c)));rewrite rmorphM -hTriangle.
      exact:(@ring_submodule_scale M V W hLaws (eta a) (include c) hC).
  have hGenerators:[set c:C|c \in F] `<=` P.
    move=>c hC;apply:(generated_ring_submodule_contains hW).
    apply/mapP;by exists c.
  have hAll:=generated_ring_submodule_minimal hF hP hGenerators.
  move=>c;exact:hAll c I.
have hStable (c:C):forall u:L,W u ->W (include c*u).
  pose N:set V:=fun u=>W (include c*u).
  have hN:is_ring_submodule N.
    constructor.
    - change (W (include c*0));rewrite mulr0;exact:ring_submodule_zero hLaws.
    - move=>u v hU hV;change (W (include c*(u+v)));rewrite mulrDr.
      exact:(@ring_submodule_add M V W hLaws _ _ hU hV).
    - move=>u hU;change (W (include c*(-u)));rewrite mulrN.
      exact:(@ring_submodule_opp M V W hLaws _ hU).
    - move=>a u hU;change (W (include c*(phi a*u)));rewrite mulrCA.
      exact:(@ring_submodule_scale M V W hLaws a (include c*u) hU).
  have hGenerators:[set u:V|u \in images] `<=` N.
    move=>u /mapP [d hD ->];change (W (include c*include d)).
    rewrite -rmorphM;exact:hOriginal (c*d).
  move=>u hU;exact:(@generated_ring_submodule_minimal M V [set v|v \in images] W hW N hN hGenerators u hU).
have hOne:W (1:L) by rewrite -(rmorph1 include);exact:hOriginal 1.
pose S:subspace V:=@Subspace M V W (ring_submodule_zero hLaws)
  (@ring_submodule_add M V W hLaws) (@ring_submodule_scale M V W hLaws).
have hImage:forall v:V,W v <->exists w:subspace_space S,subspace_val w = v.
  move=>v;split.
  - move=>hV;exists (@subspace_lift M V S v hV);reflexivity.
  - move=>[w <-];exact:subspace_valP w.
have hFiniteW:is_finitely_generated_ring_submodule W by exists images.
have hCarrierFinite:=@ring_module_finite_injective_lift M V [the lmodType M of subspace_space S]
  (@subspace_inclusion M V S) W (@subspace_val_injective M V S) hImage hFiniteW.
have [n [basis hBasis]]:=@finitely_generated_field_module_basis M [the lmodType M of subspace_space S] hCarrierFinite.
have hInverse (b:C) (hB:b<>0):W ((include b)^-1).
  have hNonzero:include b<>0.
    move=>hZero;apply:hB;apply:(fraction_field_embedding_injective hFraction);by rewrite hZero rmorph0.
  exact:(@finite_invariant_coefficient_subspace_inverse M L phi S n basis hBasis (include b)
    hOne hNonzero (hStable b)).
have hWhole:forall z:L,W z.
  move=>z;have [a [b [hB hZ]]]:=fraction_field_fraction_representation hFraction z.
  rewrite hZ;exact:hStable a ((include b)^-1) (hInverse b hB).
have hSets:W = setT.
  apply:funext=>z;apply:propext;split=>_;[exact:I|exact:hWhole z].
rewrite -hSets;exists images;exact:hW.
Qed.
