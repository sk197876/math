(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    actual transverse kernel has dimension n minus one.
    A finite image basis and the original line splitting
    prove this fact. No basis of the sealed kernel
    is supplied as an additional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed Hom RealNormUP LinearBasis FiniteSpans FiniteBasisCriterion
  FiniteBasisComparison FiniteIndependence InfiniteSequence FiniteSurjectiveImageBasis
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_transverse_basis_exists]:
    im eta is isomorphic to C^(n-1), 3.4.7,
    p. 325. In source dimension n+1 the
    original transverse space has a basis of exactly
    n vectors, including n=0. *)
Theorem complex_weierstrass_transverse_basis_exists (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (v:X) (xi:Hom X (ComplexScalars.C R)^o)
    (inclusion:Hom K X) (projection:Hom X K) n (e:'I_n.+1->X):
  is_basis e ->is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  exists f:'I_n->K,is_basis f.
Proof.
move=>he hSplit.
have hSurjective z:exists x:X,projection x = z.
  exists (inclusion z);exact:(complex_weierstrass_transverse_left_inverse hSplit z).
have [m [f hf]]:=finite_surjective_image_basis_exists he hSurjective.
pose g:=fun i:'I_m=>inclusion (f i).
have hInclusion:injective inclusion:=complex_weierstrass_inclusion_injective hSplit.
have hG:finite_independent g.
  exact:(@finite_independent_map (ComplexScalars.C R) [the finType of 'I_m] K X
    (hom_as_linear inclusion) f hInclusion (finite_basis_independent hf)).
have hOutside c:v!=\sum_(i<m) c i*:g i.
  apply/eqP=>h;have hh:=congr1 xi h.
  rewrite (complex_weierstrass_transverse_functional_value hSplit) linear_sum in hh.
  have hZero:(\sum_(i<m) xi (c i*:g i)) = 0.
    apply:big1=>i _.
    have hLineLinear:xi (c i*:g i+0) = c i*xi (g i)+xi 0:=hom_linear xi (c i) (g i) 0.
    rewrite addr0 linear0 addr0 /g (complex_weierstrass_transverse_kernel hSplit) mulr0 in hLineLinear.
    exact:hLineLinear.
  rewrite hZero in hh.
  have h10:(1:ComplexScalars.C R)!=0:=oner_neq0 (ComplexScalars.C R).
  by rewrite hh eqxx in h10.
pose b:=ordinal_snoc g v.
have hIndependent:finite_independent b:=finite_independent_snoc hG hOutside.
have hIncluded z:in_finite_span g (inclusion z).
  apply:(@basis_induction (ComplexScalars.C R) (Choice.clone 'I_m _) K f hf (fun z=>in_finite_span g (inclusion z)))=>[|x y hx hy|a x hx|i].
  - rewrite linear0;exact:in_finite_span_zero.
  - rewrite linearD;exact:in_finite_span_add hx hy.
  - rewrite linearZ;exact:(@in_finite_span_scale (ComplexScalars.C R) X m g a (inclusion x) hx).
  - exists (fun j=>if j==i then (1:ComplexScalars.C R) else 0).
    rewrite (bigD1 i) //= eqxx scale1r.
    have hRest:(\sum_(j<m|j!=i) (if j==i then (1:ComplexScalars.C R) else 0)*:g j) = 0.
      apply:big1=>j hj;by rewrite (negbTE hj) scale0r.
    by rewrite hRest addr0.
have hBasis:is_basis b.
  apply:(@finite_basis_criterion (ComplexScalars.C R) [the finType of 'I_m.+1] X b hIndependent)=>x.
  have hFirst:=@in_finite_span_snoc (ComplexScalars.C R) X m g v (inclusion (projection x))
    (hIncluded (projection x)).
  have hLast:=@in_finite_span_scale (ComplexScalars.C R) X m.+1 b (xi x) v (@in_finite_span_last (ComplexScalars.C R) X m g v).
  have hSum:=in_finite_span_add hFirst hLast.
  rewrite (complex_weierstrass_transverse_projection_equation hSplit) subrK in hSum.
  exact:hSum.
have hSize:=finite_basis_size hBasis he.
have hmn:m = n by exact:succn_inj hSize.
subst m;by exists f.
Qed.
