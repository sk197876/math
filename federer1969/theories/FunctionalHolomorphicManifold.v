(** Federer (1969), 3.4.12, p. 339: functional holomorphic
    submanifolds have the original local straightening charts. Reuse
    independent covector completion and the existing joint holomorphic
    inverse. The source plane and both inverse equations remain actual. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction
  NormDifferentialUP NormDifferentialLocal NormBoundedLinearTopology NormFiniteLinearBound NormOpenDomainLaws
  NormAnalyticLocal NormRegularity NormClassOneUP NormClassZeroNonzeroLocus NormDiffeomorphismUP
  ModuleQuotient GrassmannSubspaces HolomorphicDiffeomorphismUP HolomorphicSubmanifoldUP
  FunctionalHolomorphicSubmanifoldUP FieldComplementaryCovectors FieldBlockLinearMaps FieldFirstCoordinatePlane FiniteHolomorphicJointInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [functional_holomorphic_submanifold_charts_at_bound]:
    the functional definition gives the straightening definition,
    3.4.12, p. 339. The dimension bound is already a
    clause of the original functional definition. *)
Theorem functional_holomorphic_submanifold_charts_at_bound (R:realType) n m (hMN:(m<=n)%N):
  forall U S:set (coordinate_space (ComplexScalars.C R) n),
  @is_functional_holomorphic_submanifold R n m U S ->
  @is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n)
    (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m S.
Proof.
have hSize:n = (m+(n-m))%N by rewrite subnKC.
rewrite hSize /is_functional_holomorphic_submanifold addKn.
move=>U S [hDimension [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]] a ha.
pose C:=ComplexScalars.C R.
pose l:=(n-m)%N.
pose X:=coordinate_space C (m+l).
pose Y:=coordinate_space C m.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose YR:=restricted_space (ComplexScalars.embed R) Y.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose NX:=@holomorphic_coordinate_norm R (m+l).
pose NY:=@holomorphic_coordinate_norm R m.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R (m+l)).
pose hNY:=complex_norm_real (@holomorphic_coordinate_norm_laws R m).
have [hUa [hZeros hNonzero]]:=(hEquation a).1 ha.
have [D [hD hIndependent]]:=hDifferentials a ha.
have hComplement:exists P:Hom X Y,forall x,P x = 0 ->(forall i,D i x = 0) ->x=0.
  have h:=@field_complementary_covectors C X (m+l) m
    (@coordinate_basis C (m+l)) (@coordinate_basisP C (m+l)) hDimension.
  rewrite addKn in h;exact:h D hIndependent.
have [P hSeparate]:=hComplement.
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (m+l+(m+l))
  (ordered_real_basis (@coordinate_basis C (m+l)))
  (ordered_real_basisP (@coordinate_basisP C (m+l))) (complex_hom_real P).
pose A:set X:=fun x=>U x /\g x!=0.
have hOpen:=@norm_class_zero_nonzero_locus_open R XR CR NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) U g
  (norm_class_continuous (norm_analytic_class_all_orders hG.1 0%N)).
have hA x (hx:A x):@norm_domain_interior R XR NX A x.
  have hNear:=hOpen;rewrite openE in hNear.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX A x).2 (hNear x hx).
have hAA:A a by split;last by apply/eqP.
have hFA i:=@holomorphic_open_restriction R X C^o NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) U A (f i) (fun x hx=>hx.1) hA (hF i).
have hDA i:@has_norm_differential R XR CR NX (@complex_modulus R) A (f i) a (complex_hom_real (D i)).
  exact:(@norm_differential_restrict R XR CR NX (@complex_modulus R) U A (f i) a
    (complex_hom_real (D i)) (fun x hx=>hx.1) (hA a hAA) (hD i)).
have hSeparateA u:P u = 0 ->(forall i,complex_hom_real (D i) u = 0) ->u=0.
  exact:hSeparate u.
have [H [G [r [hFirst [hLast [hH [hR [hInto [hInverse hBackward]]]]]]]]]:=
  @finite_holomorphic_joint_inverse R m l A hA P hPBound f hFA a hAA
    (fun i=>complex_hom_real (D i)) hDA hSeparateA.
pose T:set X:=[set x|NX (x-a)<r].
have hAt:NX (a-a) = 0.
  rewrite subrr;exact:real_seminorm_zero hNX.1.
have hTa:T a by change (NX (a-a)<r);rewrite hAt.
have hT:@norm_domain_interior R XR NX T a:=@norm_open_ball_domain_interior R XR NX hNX a r a hTa.
have hTAll x (hx:T x):@norm_domain_interior R XR NX T x.
  exact:(@norm_open_ball_domain_interior R XR NX hNX a r x hx).
have hForward:=@holomorphic_open_restriction R X X NX NX hNX hNX A T H hInto hTAll hH.
have hDiffeom:@is_holomorphic_diffeomorphism R X NX hNX T (H @` T) H G.
  constructor;try exact:hForward;try exact:hBackward.
  - exact:norm_diffeomorphism_maps hInverse.
  - exact:norm_diffeomorphism_inverse_maps hInverse.
  - exact:norm_diffeomorphism_left_inverse hInverse.
  - exact:norm_diffeomorphism_right_inverse hInverse.
have [Z hZ]:=@field_first_coordinate_plane C l m.
have hPlane x (hx:T x):S x <->grassmann_val Z (H x).
  rewrite hZ;split.
  - move=>hSx;apply/ffunP=>i.
    rewrite hLast ffunE;exact:((hEquation x).1 hSx).2.1 i.
  - move=>hZero;apply:(hEquation x).2;split;first exact:(hInto x hx).1.
    split;last by apply/eqP;exact:(hInto x hx).2.
    move=>i;have h:=congr1 (fun y:coordinate_space C l=>y i) hZero.
    by rewrite hLast ffunE in h.
exists T,(H @` T),H,G,Z;split;first exact:hT.
split;first exact:hDiffeom.
apply/seteqP;split.
- move=>y [x [hSx hTx] <-];split;first exact:(hPlane x hTx).1 hSx.
  by exists x.
- move=>y [hZy [x hTx hxy]];exists x;last exact:hxy.
  split;last exact:hTx;apply:(hPlane x hTx).2.
  by rewrite hxy.
Qed.
(** Source for [functional_holomorphic_submanifold_holomorphic]: every
    original functional holomorphic submanifold has the stated complex
    dimension in the straightening definition, 3.4.12, p. 339.
    No extra rank or dimension hypothesis is imposed. *)
Theorem functional_holomorphic_submanifold_holomorphic (R:realType) n m
    (U S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_functional_holomorphic_submanifold R n m U S ->
  @is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n)
    (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m S.
Proof. move=>h;exact:(functional_holomorphic_submanifold_charts_at_bound h.1 h). Qed.
